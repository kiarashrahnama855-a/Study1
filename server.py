#!/usr/bin/env python3
"""Vexta lightweight HTTP application. Review security and persistence before public production use."""
from http.server import ThreadingHTTPServer, SimpleHTTPRequestHandler
from urllib.parse import urlparse, parse_qs, unquote
from pathlib import Path
from datetime import datetime, timezone, timedelta
import sqlite3, json, secrets, mimetypes, threading, time, re, base64, zipfile, io, uuid, os, hashlib, shutil
from urllib.parse import quote
try:
    from pypdf import PdfReader
except Exception:
    PdfReader=None

ROOT=Path(__file__).resolve().parent
DB=ROOT/'data'/'vexta.db'
UPLOADS=ROOT/'uploads'
ADMIN_PHONE='09116620513'
# PBKDF2-SHA256 hash only; override with VEXTA_ADMIN_PASSWORD_HASH in production.
ADMIN_PASSWORD_HASH=os.environ.get('VEXTA_ADMIN_PASSWORD_HASH','pbkdf2_sha256$310000$nOfI_2ifKpCg73h-QSnwvw$MBOTFmlSvAdEWXzkOxC0d-uRH7A_1wrreLUUNsMBmLA')
SESSIONS={}
LOCK=threading.RLock()
ENTITIES={'customers','products','subscriptions','orders','wallet','receipts','discounts','referrals','files','tickets','settings','token_transactions','money_transactions','devices','device_violations','device_change_requests','security_events'}

def now(): return datetime.now(timezone.utc)
def iso(dt=None): return (dt or now()).isoformat(timespec='seconds')
def db():
    c=sqlite3.connect(DB,timeout=20); c.row_factory=sqlite3.Row
    c.execute('PRAGMA busy_timeout=20000')
    return c

def init_db():
    ROOT.joinpath('data').mkdir(exist_ok=True)
    c=db()
    c.execute('PRAGMA journal_mode=WAL')
    c.execute('PRAGMA synchronous=NORMAL')
    c.execute('''CREATE TABLE IF NOT EXISTS records(id INTEGER PRIMARY KEY AUTOINCREMENT, entity TEXT NOT NULL, owner TEXT, data TEXT NOT NULL, created_at TEXT NOT NULL, updated_at TEXT NOT NULL)''')
    c.execute('CREATE INDEX IF NOT EXISTS idx_entity ON records(entity)')
    c.execute('CREATE INDEX IF NOT EXISTS idx_entity_owner_id ON records(entity,owner,id)')
    c.execute("DELETE FROM records WHERE entity='events' OR entity='messages' OR (entity='notifications' AND owner='admin')")
    c.commit(); c.close()
def decode(r): return {'id':r['id'],'owner':r['owner'],'data':json.loads(r['data']),'created_at':r['created_at'],'updated_at':r['updated_at']}
def add(entity,data,owner=None):
    with LOCK:
        c=db(); t=iso(); cur=c.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',(entity,owner,json.dumps(data,ensure_ascii=False),t,t)); rid=cur.lastrowid; c.commit(); c.close()
    return rid
def rows(entity,owner=None):
    c=db(); q='SELECT * FROM records WHERE entity=?'; args=[entity]
    if owner is not None: q+=' AND owner=?'; args.append(str(owner))
    q+=' ORDER BY id DESC'; out=[decode(x) for x in c.execute(q,args).fetchall()]; c.close(); return out
def update(entity,rid,data):
    with LOCK:
        c=db(); cur=c.execute('UPDATE records SET data=?,updated_at=? WHERE id=? AND entity=?',(json.dumps(data,ensure_ascii=False),iso(),rid,entity)); ok=cur.rowcount>0; c.commit(); c.close(); return ok
def get(entity,rid):
    c=db(); r=c.execute('SELECT * FROM records WHERE id=? AND entity=?',(rid,entity)).fetchone(); c.close(); return decode(r) if r else None

def customer_has_active_product(customer_id, product_id):
    for sub in rows('subscriptions',str(customer_id)):
        sd=sub['data']
        try:
            if sd.get('status') in ('فعال','فعال - پرداخت‌نشده') and int(sd.get('product_id',0))==int(product_id) and (not sd.get('end_at') or datetime.fromisoformat(sd['end_at'])>now()):
                return True
        except Exception:
            continue
    return False

def pdf_blob_for(session, source, rid):
    """Return bytes only after checking the role and record ownership."""
    source=str(source or '')
    rec=None; raw=''
    if source=='files':
        rec=get('files',int(rid))
        if not rec or rec['data'].get('type')!='PDF': return None,'فایل PDF پیدا نشد.'
        if session.get('role')=='customer':
            if str(rec.get('owner'))!=str(session.get('customer_id')): return None,'دسترسی به این فایل مجاز نیست.'
            if not customer_has_active_product(session['customer_id'],rec['data'].get('product_id',0)): return None,'اشتراک مرتبط با این فایل فعال نیست.'
        elif session.get('role')!='admin': return None,'دسترسی مجاز نیست.'
        launch=rec['data'].get('launch_url') or rec['data'].get('stored_url') or ''
        path=urlparse(launch).path
        target=(ROOT/unquote(path.lstrip('/'))).resolve()
        base=(UPLOADS/'published').resolve()
        if base not in target.parents or not target.is_file(): return None,'فایل PDF روی سرور پیدا نشد.'
        try: return target.read_bytes(),None
        except OSError: return None,'خواندن فایل PDF ناموفق بود.'
    if source in ('wallet','receipts'):
        rec=get(source,int(rid))
        if not rec: return None,'فیش پیدا نشد.'
        if session.get('role')=='customer' and str(rec.get('owner'))!=str(session.get('customer_id')): return None,'دسترسی به این فیش مجاز نیست.'
        if session.get('role') not in ('admin','customer'): return None,'دسترسی مجاز نیست.'
        raw=rec['data'].get('receipt_file_data' if source=='wallet' else 'file_data','') or ''
        if not raw.startswith('data:application/pdf;'): return None,'این فیش از نوع PDF نیست.'
        try:
            payload=raw.split(',',1)[1]
            return base64.b64decode(payload,validate=False),None
        except Exception: return None,'داده PDF معتبر نیست.'
    return None,'منبع فایل نامعتبر است.'

def normalize_search_text(value):
    return str(value or '').replace('ي','ی').replace('ك','ک').replace('ـ','').casefold()
def log(actor,action,detail=''):
    # دفتر وقایع مدیریتی عمداً حذف شده؛ تاریخچه مالی جداگانه در token_transactions نگهداری می‌شود.
    return None

def atomic_token_change(customer_id, delta, reason, reference=None):
    """Atomic balance update + immutable token transaction; idempotent by reference."""
    with LOCK:
        c=db()
        try:
            c.execute('BEGIN IMMEDIATE')
            if reference:
                prior=c.execute("SELECT id FROM records WHERE entity='token_transactions' AND json_extract(data,'$.reference')=?",(str(reference),)).fetchone()
                if prior:
                    c.rollback(); return False, 'duplicate'
            row=c.execute("SELECT * FROM records WHERE entity='customers' AND id=?",(int(customer_id),)).fetchone()
            if not row: c.rollback(); return False, 'customer_missing'
            cd=json.loads(row['data']); balance=int(cd.get('tokens',0)); delta=int(delta)
            if balance+delta<0: c.rollback(); return False, 'insufficient'
            cd['tokens']=balance+delta
            c.execute('UPDATE records SET data=?,updated_at=? WHERE id=?',(json.dumps(cd,ensure_ascii=False),iso(),int(customer_id)))
            t=iso(); payload={'customer_id':int(customer_id),'delta':delta,'balance_after':balance+delta,'reason':reason,'reference':str(reference or ''),'time':t}
            c.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',('token_transactions',str(customer_id),json.dumps(payload,ensure_ascii=False),t,t))
            c.commit(); return True, balance+delta
        except Exception:
            c.rollback(); raise
        finally: c.close()

def atomic_customer_adjustment(customer_id, token_delta, wallet_delta, reason, reference):
    with LOCK:
        c=db()
        try:
            c.execute('BEGIN IMMEDIATE')
            row=c.execute("SELECT * FROM records WHERE entity='customers' AND id=?",(int(customer_id),)).fetchone()
            if not row:c.rollback();return False,'missing'
            cd=json.loads(row['data']);tokens=int(cd.get('tokens',0));wallet=int(cd.get('wallet',0));td=int(token_delta);wd=int(wallet_delta)
            if tokens+td<0 or wallet+wd<0:c.rollback();return False,'insufficient'
            cd['tokens']=tokens+td;cd['wallet']=wallet+wd;t=iso()
            c.execute('UPDATE records SET data=?,updated_at=? WHERE id=?',(json.dumps(cd,ensure_ascii=False),t,int(customer_id)))
            if td:
                tx={'customer_id':int(customer_id),'delta':td,'balance_after':tokens+td,'reason':reason,'reference':'token:'+str(reference),'time':t}
                c.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',('token_transactions',str(customer_id),json.dumps(tx,ensure_ascii=False),t,t))
            if wd:
                tx={'customer_id':int(customer_id),'delta':wd,'balance_after':wallet+wd,'reason':reason,'reference':'wallet:'+str(reference),'time':t}
                c.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',('money_transactions',str(customer_id),json.dumps(tx,ensure_ascii=False),t,t))
            c.commit();return True,cd
        except Exception:c.rollback();raise
        finally:c.close()

def atomic_purchase_subscription(customer_id, token_amount, reason, reference, subscription_data):
    with LOCK:
        c=db()
        try:
            c.execute('BEGIN IMMEDIATE')
            prior=c.execute("SELECT id FROM records WHERE entity='token_transactions' AND json_extract(data,'$.reference')=?",(str(reference),)).fetchone()
            if prior:c.rollback();return False,'duplicate'
            row=c.execute("SELECT * FROM records WHERE entity='customers' AND id=?",(int(customer_id),)).fetchone()
            if not row:c.rollback();return False,'customer_missing'
            cd=json.loads(row['data']);balance=int(cd.get('tokens',0));delta=int(token_amount);cd['tokens']=balance+delta;t=iso()
            c.execute('UPDATE records SET data=?,updated_at=? WHERE id=?',(json.dumps(cd,ensure_ascii=False),t,int(customer_id)))
            tx={'customer_id':int(customer_id),'delta':delta,'balance_after':balance+delta,'reason':reason,'reference':str(reference),'time':t}
            c.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',('token_transactions',str(customer_id),json.dumps(tx,ensure_ascii=False),t,t))
            sd=dict(subscription_data);sd['customer_id']=int(customer_id)
            c.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',('subscriptions',str(customer_id),json.dumps(sd,ensure_ascii=False),t,t))
            c.commit();return True,balance+delta
        except Exception:c.rollback();raise
        finally:c.close()

def atomic_publish_assignment(customer_id, cost, reason, reference, filedata):
    with LOCK:
        c=db()
        try:
            c.execute('BEGIN IMMEDIATE')
            prior=c.execute("SELECT id FROM records WHERE entity='token_transactions' AND json_extract(data,'$.reference')=?",(str(reference),)).fetchone()
            if prior:c.rollback();return False,'duplicate'
            row=c.execute("SELECT * FROM records WHERE entity='customers' AND id=?",(int(customer_id),)).fetchone()
            if not row:c.rollback();return False,'customer_missing'
            cd=json.loads(row['data']); balance=int(cd.get('tokens',0)); cost=int(cost)
            if balance<cost:c.rollback();return False,'insufficient'
            cd['tokens']=balance-cost;t=iso()
            c.execute('UPDATE records SET data=?,updated_at=? WHERE id=?',(json.dumps(cd,ensure_ascii=False),t,int(customer_id)))
            tx={'customer_id':int(customer_id),'delta':-cost,'balance_after':balance-cost,'reason':reason,'reference':str(reference),'time':t}
            c.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',('token_transactions',str(customer_id),json.dumps(tx,ensure_ascii=False),t,t))
            fd=dict(filedata);fd['token_cost']=cost
            c.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',('files',str(customer_id),json.dumps(fd,ensure_ascii=False),t,t))
            c.commit();return True,balance-cost
        except Exception:c.rollback();raise
        finally:c.close()

def atomic_wallet_change(customer_id, delta, reason, reference=None):
    with LOCK:
        c=db()
        try:
            c.execute('BEGIN IMMEDIATE')
            if reference:
                prior=c.execute("SELECT id FROM records WHERE entity='money_transactions' AND json_extract(data,'$.reference')=?",(str(reference),)).fetchone()
                if prior:c.rollback();return False,'duplicate'
            row=c.execute("SELECT * FROM records WHERE entity='customers' AND id=?",(int(customer_id),)).fetchone()
            if not row:c.rollback();return False,'customer_missing'
            cd=json.loads(row['data']); balance=int(cd.get('wallet',0)); delta=int(delta)
            if balance+delta<0:c.rollback();return False,'insufficient'
            cd['wallet']=balance+delta;c.execute('UPDATE records SET data=?,updated_at=? WHERE id=?',(json.dumps(cd,ensure_ascii=False),iso(),int(customer_id)))
            t=iso(); payload={'customer_id':int(customer_id),'delta':delta,'balance_after':balance+delta,'reason':reason,'reference':str(reference or ''),'time':t}
            c.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',('money_transactions',str(customer_id),json.dumps(payload,ensure_ascii=False),t,t));c.commit();return True,balance+delta
        except Exception:c.rollback();raise
        finally:c.close()

def atomic_review_wallet_request(request_id, approved, reason=''):
    with LOCK:
        c=db()
        try:
            c.execute('BEGIN IMMEDIATE')
            rr=c.execute("SELECT * FROM records WHERE entity='wallet' AND id=?",(int(request_id),)).fetchone()
            if not rr:c.rollback();return False,'missing'
            rd=json.loads(rr['data'])
            if rd.get('status') not in ('در انتظار بررسی','در انتظار برداشت'):c.rollback();return False,'reviewed'
            customer_id=int(rd.get('customer_id',0)); amount=int(rd.get('amount',0)); typ=rd.get('type');
            if approved:
                cr=c.execute("SELECT * FROM records WHERE entity='customers' AND id=?",(customer_id,)).fetchone()
                if not cr:c.rollback();return False,'customer_missing'
                cd=json.loads(cr['data']);balance=int(cd.get('wallet',0));delta=amount if typ=='شارژ' else -amount if typ=='برداشت' else 0
                if balance+delta<0:c.rollback();return False,'insufficient'
                cd['wallet']=balance+delta;t=iso()
                c.execute('UPDATE records SET data=?,updated_at=? WHERE id=?',(json.dumps(cd,ensure_ascii=False),t,customer_id))
                tx={'customer_id':customer_id,'delta':delta,'balance_after':balance+delta,'reason':'درخواست کیف پول: '+str(typ),'reference':'wallet-request:'+str(request_id),'time':t}
                c.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',('money_transactions',str(customer_id),json.dumps(tx,ensure_ascii=False),t,t))
            else:t=iso()
            rd.update({'status':'تأییدشده' if approved else 'ردشده','reviewed_at':t,'review_reason':reason})
            if approved: rd['receipt_file_data']=''
            c.execute('UPDATE records SET data=?,updated_at=? WHERE id=?',(json.dumps(rd,ensure_ascii=False),t,int(request_id)))
            c.commit();return True,customer_id
        except Exception:c.rollback();raise
        finally:c.close()

def analyze_learning_file(blob, filename, ext):
    texts=[]; pages=0
    try:
        if ext=='.pdf' and PdfReader:
            reader=PdfReader(io.BytesIO(blob));pages=len(reader.pages)
            for page in reader.pages[:30]: texts.append(page.extract_text() or '')
        elif ext=='.zip':
            with zipfile.ZipFile(io.BytesIO(blob)) as z:
                infos=z.infolist()
                if len(infos)>500 or sum(i.file_size for i in infos)>100*1024*1024: raise ValueError('حجم ZIP بیش از حد مجاز است.')
                for info in infos[:150]:
                    if Path(info.filename).suffix.lower() in ('.html','.htm','.txt','.md','.json') and info.file_size<2*1024*1024:
                        texts.append(z.read(info).decode('utf-8','ignore'))
        elif ext in ('.html','.htm'): texts.append(blob.decode('utf-8','ignore'))
    except Exception: pass
    text=' '.join(texts)
    clean=re.sub(r'<script[\s\S]*?</script>|<style[\s\S]*?</style>|<[^>]+>',' ',text,flags=re.I)
    words=re.findall(r'[A-Za-z0-9_آ-ی]+',clean)
    questions=clean.count('?')+clean.count('؟')+len(re.findall(r'<input[^>]+type=[\"\']radio',text,re.I))
    terms=['اثبات','تحلیل','استنتاج','مشتق','انتگرال','معادله','قضیه','مقایسه','evaluate','derive','proof','integral','derivative','algorithm','complexity']
    complex_hits=sum(len(re.findall(re.escape(t),clean,re.I)) for t in terms)
    formulas=sum(clean.count(x) for x in ('=','∑','√','∫','≤','≥','→','±'))
    score=len(words)/900 + questions*.55 + complex_hits*.8 + formulas*.25
    if score<1.2: difficulty='آسان'
    elif score<3.2: difficulty='متوسط'
    elif score<6.5: difficulty='سخت'
    else: difficulty='بسیار سخت'
    if not text and ext=='.pdf':
        score=pages*.35+len(blob)/(1024*1024)*.4
        difficulty='آسان' if score<2 else 'متوسط' if score<5 else 'سخت' if score<10 else 'بسیار سخت'
    return {'difficulty':difficulty,'word_count':len(words),'question_marks':questions,'complex_terms':complex_hits,'formula_signals':formulas,'pages':pages,'method':'تحلیل محلی متن و شاخص‌های ساختاری؛ مدل زبانی خارجی نیست.'}

def safe_extract_zip(data, destination):
    root=Path(destination).resolve(); root.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        infos=z.infolist()
        if len(infos)>500 or sum(x.file_size for x in infos)>100*1024*1024: raise ValueError('حجم بازشده یا تعداد فایل‌های ZIP بیش از حد مجاز است.')
        for info in infos:
            target=(root/info.filename).resolve()
            if root not in target.parents and target!=root: raise ValueError('مسیر نامعتبر داخل ZIP شناسایی شد.')
            if info.is_dir(): target.mkdir(parents=True,exist_ok=True); continue
            target.parent.mkdir(parents=True,exist_ok=True)
            with z.open(info) as src, open(target,'wb') as dst: dst.write(src.read())
    candidates=list(root.rglob('index.html'))
    return candidates[0].parent if candidates else root
def notify(owner,title,body,kind='info'):
    # مدیریت اعلان مستقل ندارد؛ اعلان‌های ضروری مشتری حفظ می‌شوند.
    if owner is None or str(owner)=='admin': return None
    add('notifications',{'title':title,'body':body,'kind':kind,'read':False,'time':iso()},str(owner))
def unique_discount_code(prefix='VXR'):
    for _ in range(20):
        candidate=prefix+secrets.token_hex(5).upper()
        if not any(str(x['data'].get('code','')).upper()==candidate for x in rows('discounts')):
            return candidate
    raise RuntimeError('ساخت کد تخفیف یکتا ناموفق بود.')

def ensure_customer(phone,name='',referral_code=''):
    for r in rows('customers'):
        if r['data'].get('phone')==phone and r['data'].get('status')!='حذف‌شده':
            cd=r['data']
            if not cd.get('referral_code'):
                cd['referral_code']='VX'+secrets.token_hex(3).upper();update('customers',r['id'],cd);r=get('customers',r['id'])
            return r
    inviter=None
    if referral_code:
        inviter=next((x for x in rows('customers') if str(x['data'].get('referral_code','')).upper()==str(referral_code).strip().upper()),None)
        if inviter and inviter['data'].get('phone')==phone: inviter=None
    data={'name':name or 'کاربر Vexta','phone':phone,'status':'فعال','wallet':0,'debt':0,'tokens':0,'joined_at':iso(),'referral_code':'VX'+secrets.token_hex(3).upper(),'referral_discount':0,'referral_discount_used':False,'referred_by':inviter['id'] if inviter else None}
    rid=add('customers',data)
    if inviter:
        iv=inviter['data'];iv['referral_discount']=0;iv['referral_discount_used']=True;update('customers',inviter['id'],iv)
        reward_code=unique_discount_code('VXR')
        add('discounts',{'code':reward_code,'kind':'درصدی','value':15,'status':'فعال','limit':1,'used':0,'used_by':[],'expires_at':'','source':'referral','description':'پاداش معرفی موفق یک دوست'},str(inviter['id']))
        add('referrals',{'inviter_id':inviter['id'],'inviter':iv.get('name'),'customer_id':rid,'friend_phone':phone,'code':referral_code,'reward_code':reward_code,'status':'موفق','created_at':iso()},str(inviter['id']))
        notify(inviter['id'],'کد تخفیف معرفی دوستان صادر شد',f'به‌پاس معرفی موفق دوستت، کد تخفیف اختصاصی ۱۵ درصدی {reward_code} برایت فعال شد.','success')
    return get('customers',rid)

def reminders():
    """Create once-only reminders for pending orders with 24h or less remaining."""
    try:
        for o in rows('orders'):
            d=o['data']; due=d.get('due_at')
            if not due or d.get('status') not in ('در انتظار پرداخت','فعال - پرداخت‌نشده','در انتظار بررسی') or d.get('reminder_sent'): continue
            try: left=datetime.fromisoformat(due)-now()
            except: continue
            if timedelta(0)<left<=timedelta(hours=24):
                cust=get('customers',int(d.get('customer_id',0)))
                if cust:
                    notify(cust['id'],'یادآوری مهلت پرداخت',f"کمتر از ۲۴ ساعت تا پایان مهلت پرداخت سفارش {d.get('code','')} باقی مانده است.",'warning')
                d['reminder_sent']=True; update('orders',o['id'],d)
            elif left<=timedelta(0) and not d.get('deadline_notice_sent'):
                d['deadline_notice_sent']=True; update('orders',o['id'],d)
                notify(d.get('customer_id'),'پایان مهلت پرداخت','مهلت پرداخت سفارش شما به پایان رسیده است. برای پیگیری از راه ارتباطی اعلام‌شده با مدیریت تماس بگیر.','danger')
    except Exception as e: print('reminder error:',e)
def cleanup_expired_uploads():
    """Remove all uploaded attachments and published files 96 hours after upload."""
    try:
        cutoff=now()-timedelta(days=4)
        seen=set()
        for rec in rows('files'):
            data=rec.get('data',{}); fid=str(data.get('file_id') or '')
            if not fid or fid in seen: continue
            seen.add(fid)
            stamp=data.get('published_at')
            if not stamp: continue
            try: uploaded=datetime.fromisoformat(str(stamp).replace('Z','+00:00'))
            except Exception: continue
            if uploaded.tzinfo is None: uploaded=uploaded.replace(tzinfo=timezone.utc)
            if uploaded>cutoff: continue
            folder=(UPLOADS/'published'/fid).resolve(); base=(UPLOADS/'published').resolve()
            if base in folder.parents and folder.exists(): shutil.rmtree(folder,ignore_errors=True)
            with LOCK:
                con=db()
                try:
                    con.execute("DELETE FROM records WHERE entity='files' AND json_extract(data,'$.file_id')=?",(fid,))
                    con.commit()
                finally: con.close()
        # Payment attachments are removed from the database too; financial rows remain.
        for entity,field,time_fields in (('wallet','receipt_file_data',('created_at','uploaded_at')),('receipts','file_data',('sent_at','created_at','uploaded_at'))):
            for rec in rows(entity):
                data=rec.get('data',{})
                if not str(data.get(field,'')).startswith('data:'): continue
                stamp=next((data.get(k) for k in time_fields if data.get(k)),None)
                if not stamp: continue
                try: uploaded=datetime.fromisoformat(str(stamp).replace('Z','+00:00'))
                except Exception: continue
                if uploaded.tzinfo is None: uploaded=uploaded.replace(tzinfo=timezone.utc)
                if uploaded<=cutoff:
                    data[field]=''
                    update(entity,rec['id'],data)
    except Exception as exc: print('upload cleanup error:',exc)

def scheduler():
    while True:
        reminders(); cleanup_expired_uploads(); time.sleep(60)

class Handler(SimpleHTTPRequestHandler):
    def __init__(self,*a,**kw): super().__init__(*a,directory=str(ROOT),**kw)
    def log_message(self,*a): pass
    def sendj(self,obj,status=200):
        b=json.dumps(obj,ensure_ascii=False).encode(); self.send_response(status); self.send_header('Content-Type','application/json; charset=utf-8'); self.send_header('Content-Length',str(len(b))); self.send_header('Cache-Control','no-store');
        if self.path.startswith('/api/auth/') and isinstance(obj,dict) and obj.get('token'):
            self.send_header('Set-Cookie','VextaSession='+obj['token']+'; HttpOnly; SameSite=Strict; Path=/')
        self.end_headers(); self.wfile.write(b)
    def sendbytes(self,raw,content_type,status=200):
        self.send_response(status); self.send_header('Content-Type',content_type); self.send_header('Content-Length',str(len(raw))); self.send_header('Cache-Control','private, no-store'); self.send_header('X-Content-Type-Options','nosniff'); self.end_headers(); self.wfile.write(raw)
    def body(self):
        n=int(self.headers.get('Content-Length','0'))
        if n>45*1024*1024: raise ValueError('حجم درخواست بیش از حد مجاز است')
        return json.loads(self.rfile.read(n) or b'{}')
    def auth(self):
        tok=self.headers.get('X-Vexta-Session','')
        if not tok:
            for part in self.headers.get('Cookie','').split(';'):
                if part.strip().startswith('VextaSession='): tok=part.strip().split('=',1)[1]; break
        return SESSIONS.get(tok)
    def require(self,role=None):
        s=self.auth()
        if not s or (role and s['role']!=role): self.sendj({'error':'دسترسی مجاز نیست؛ دوباره وارد شوید.'},401); return None
        return s
    def do_GET(self):
        p=urlparse(self.path); path=p.path
        if path=='/api/me':
            s=self.require()
            if s:
                if s['role']=='customer':
                    c=get('customers',s['customer_id']); s=dict(s); s['name']=c['data'].get('name','مشتری') if c else 'مشتری'; s['phone']=c['data'].get('phone','') if c else ''; s['customer_data']=c['data'] if c else {}
                self.sendj(s)
            return
        if path=='/api/public/products':
            self.sendj(rows('products')); return
        if path=='/api/public/payment-settings':
            vals=rows('settings'); out={x['data'].get('key'):x['data'].get('value','') for x in vals if x['data'].get('key') in ['card_number','card_holder']}
            self.sendj(out); return
        if path=='/api/customer/data':
            s=self.require('customer')
            if s:
                payload={e:rows(e,str(s['customer_id'])) for e in ['subscriptions','orders','wallet','receipts','notifications','files','tickets','referrals','token_transactions','money_transactions','device_change_requests']}
                payload['discounts']=[x for x in rows('discounts') if x.get('owner') in (None,str(s['customer_id']))]
                customer_rec=get('customers',s['customer_id']);payload['profile']=customer_rec['data'] if customer_rec else {};payload['profile_id']=customer_rec['id'] if customer_rec else None
                active_products={int(x['data'].get('product_id',0)) for x in payload['subscriptions'] if x['data'].get('status') in ('فعال','فعال - پرداخت‌نشده') and (not x['data'].get('end_at') or datetime.fromisoformat(x['data']['end_at'])>now())}
                payload['files']=[f for f in payload['files'] if int(f['data'].get('product_id',0)) in active_products]
                self.sendj(payload)
            return
        if path=='/api/pdf-file':
            session=self.require()
            if not session:return
            q=parse_qs(p.query); source=(q.get('source') or [''])[0]
            try: rid=int((q.get('id') or ['0'])[0])
            except ValueError:return self.sendj({'error':'شناسه فایل نامعتبر است.'},400)
            target=None; raw=None
            if source=='files':
                rec=get('files',rid)
                if not rec or rec['data'].get('type')!='PDF':return self.sendj({'error':'فایل PDF پیدا نشد.'},404)
                if session.get('role')=='customer':
                    if str(rec.get('owner'))!=str(session.get('customer_id')):return self.sendj({'error':'دسترسی به این فایل مجاز نیست.'},403)
                    if not customer_has_active_product(session['customer_id'],rec['data'].get('product_id',0)):return self.sendj({'error':'اشتراک مرتبط با این فایل فعال نیست.'},403)
                elif session.get('role')!='admin':return self.sendj({'error':'دسترسی مجاز نیست.'},403)
                launch=rec['data'].get('launch_url') or rec['data'].get('stored_url') or ''
                path_part=urlparse(launch).path
                target=(ROOT/unquote(path_part.lstrip('/'))).resolve(); base=(UPLOADS/'published').resolve()
                if base not in target.parents or not target.is_file():return self.sendj({'error':'فایل PDF روی سرور پیدا نشد.'},404)
            elif source in ('wallet','receipts'):
                raw,error=pdf_blob_for(session,source,rid)
                if error:return self.sendj({'error':error},403 if 'مجاز' in error else 404)
            else:return self.sendj({'error':'منبع PDF نامعتبر است.'},400)
            total=target.stat().st_size if target else len(raw)
            range_header=self.headers.get('Range','').strip(); start_byte=0; end_byte=max(0,total-1); status=200
            if range_header:
                match=re.fullmatch(r'bytes=(\d*)-(\d*)',range_header)
                if not match:return self.sendj({'error':'درخواست محدوده نامعتبر است.'},416)
                a,b=match.groups()
                if not a and not b:return self.sendj({'error':'درخواست محدوده نامعتبر است.'},416)
                if not a:
                    length=int(b); start_byte=max(0,total-length)
                else:
                    start_byte=int(a); end_byte=int(b) if b else end_byte
                if start_byte>=total or end_byte<start_byte:
                    self.send_response(416); self.send_header('Content-Range',f'bytes */{total}'); self.end_headers(); return
                end_byte=min(end_byte,total-1); status=206
            length=end_byte-start_byte+1
            self.send_response(status); self.send_header('Content-Type','application/pdf'); self.send_header('Accept-Ranges','bytes'); self.send_header('Content-Length',str(length)); self.send_header('Cache-Control','private, no-store, max-age=0'); self.send_header('X-Content-Type-Options','nosniff'); self.send_header('Content-Disposition','inline; filename="vexta-reader.pdf"'); self.send_header('Cross-Origin-Resource-Policy','same-origin')
            if status==206:self.send_header('Content-Range',f'bytes {start_byte}-{end_byte}/{total}')
            self.end_headers()
            if target:
                with open(target,'rb') as stream:
                    stream.seek(start_byte); remaining=length
                    while remaining:
                        chunk=stream.read(min(65536,remaining))
                        if not chunk:break
                        self.wfile.write(chunk); remaining-=len(chunk)
            else:self.wfile.write(raw[start_byte:end_byte+1])
            return
        if path=='/api/customer/file-view':
            s=self.require('customer')
            if not s:return
            fid=int((parse_qs(p.query).get('id') or ['0'])[0]); rec=get('files',fid)
            if not rec or str(rec.get('owner'))!=str(s['customer_id']):return self.sendj({'error':'این فایل برای حساب شما مجاز نیست.'},403)
            d=rec['data']; pid=int(d.get('product_id',0)); active_sub=any(x['data'].get('status') in ('فعال','فعال - پرداخت‌نشده') and int(x['data'].get('product_id',0))==pid and (not x['data'].get('end_at') or datetime.fromisoformat(x['data']['end_at'])>now()) for x in rows('subscriptions',str(s['customer_id'])))
            if not active_sub:return self.sendj({'error':'اشتراک مرتبط با این فایل فعال نیست.'},403)
            url=d.get('launch_url') or d.get('stored_url')
            self.sendj({'url':url,'type':d.get('type'),'name':d.get('name')}); return
        if path=='/api/admin/summary':
            s=self.require('admin')
            if not s:return
            con=db()
            try:
                customer_count=con.execute("SELECT COUNT(*) FROM records WHERE entity='customers'").fetchone()[0]
                recent=[decode(x) for x in con.execute("SELECT * FROM records WHERE entity='customers' ORDER BY id DESC LIMIT 6").fetchall()]
                receipt_count=con.execute("SELECT COUNT(*) FROM records WHERE entity='receipts'").fetchone()[0]
                pending_orders=con.execute("SELECT COUNT(*) FROM records WHERE entity='orders' AND json_extract(data,'$.status') IN ('در انتظار پرداخت','در انتظار بررسی','فعال - پرداخت‌نشده')").fetchone()[0]
                pending_wallet=con.execute("SELECT COUNT(*) FROM records WHERE entity='wallet' AND json_extract(data,'$.status') IN ('در انتظار بررسی','در انتظار برداشت')").fetchone()[0]
                paid=con.execute("SELECT COUNT(*),COALESCE(SUM(CAST(json_extract(data,'$.amount') AS INTEGER)),0) FROM records WHERE entity='orders' AND json_extract(data,'$.status') IN ('تأیید شده','پرداخت‌شده','فعال') AND json_extract(data,'$.paid_at') IS NOT NULL").fetchone()
                self.sendj({'counts':{'customers':customer_count,'receipts':receipt_count},'pending_orders':pending_orders,'pending_wallet':pending_wallet,'customers':recent,'revenue_total':paid[1],'paid_orders':paid[0]})
            finally: con.close()
            return
        if path.startswith('/api/admin/data/'):
            s=self.require('admin')
            if not s:return
            e=path.rsplit('/',1)[-1]
            if e not in ENTITIES:return self.sendj({'error':'بخش نامعتبر'},404)
            self.sendj(rows(e)); return
        if path=='/api/notifications':
            s=self.require('customer')
            if s:self.sendj(rows('notifications',str(s['customer_id'])))
            return
        if path.startswith('/uploads/published/'):
            parts=path.split('/')
            fid=parts[3] if len(parts)>3 else ''
            session=self.auth()
            allowed=False
            if session and session.get('role')=='admin': allowed=True
            elif session and session.get('role')=='customer':
                cid=str(session['customer_id'])
                allowed=any(x['data'].get('file_id')==fid for x in rows('files',cid))
                if allowed:
                    file_rec=next((x for x in rows('files',cid) if x['data'].get('file_id')==fid),None)
                    pid=int(file_rec['data'].get('product_id',0)) if file_rec else 0
                    active_sub=False
                    for sub in rows('subscriptions',cid):
                        sd=sub['data']
                        try: valid=sd.get('status') in ('فعال','فعال - پرداخت‌نشده') and int(sd.get('product_id',0))==pid and (not sd.get('end_at') or datetime.fromisoformat(sd['end_at'])>now())
                        except: valid=False
                        if valid:active_sub=True;break
                    allowed=active_sub
            if not allowed:return self.sendj({'error':'دسترسی به این فایل مجاز نیست.'},403)
            target=(ROOT/unquote(path.lstrip('/'))).resolve()
            if target.suffix.lower()=='.pdf':return self.sendj({'error':'برای مطالعه PDF از نمایشگر امن Vexta استفاده کن.'},403)
            base=(ROOT/'uploads'/'published').resolve()
            if base not in target.parents or not target.is_file():return self.sendj({'error':'فایل پیدا نشد.'},404)
            raw=target.read_bytes(); self.send_response(200); self.send_header('Content-Type',mimetypes.guess_type(str(target))[0] or 'application/octet-stream'); self.send_header('Content-Length',str(len(raw))); self.send_header('X-Content-Type-Options','nosniff'); self.send_header('Cache-Control','private, no-store'); self.end_headers(); self.wfile.write(raw); return
        if path.startswith('/data/') or path=='/server.py' or (path.startswith('/uploads/') and not path.startswith('/uploads/published/')):
            return self.sendj({'error':'دسترسی مجاز نیست.'},403)
        return super().do_GET()
    def do_POST(self):
        p=urlparse(self.path); path=p.path
        try:d=self.body()
        except Exception as e:return self.sendj({'error':str(e)},400)
        if path=='/api/auth/admin':
            phone=re.sub(r'\D','',str(d.get('phone',''))); password=str(d.get('password',''))
            if phone!=ADMIN_PHONE:return self.sendj({'error':'شماره مدیر صحیح نیست.'},403)
            try:
                algorithm,iterations,salt_text,hash_text=ADMIN_PASSWORD_HASH.split('$',3)
                if algorithm!='pbkdf2_sha256':raise ValueError('bad hash')
                salt=base64.urlsafe_b64decode(salt_text+'='*((4-len(salt_text)%4)%4)); expected=base64.urlsafe_b64decode(hash_text+'='*((4-len(hash_text)%4)%4))
                actual=hashlib.pbkdf2_hmac('sha256',password.encode(),salt,int(iterations))
                valid=secrets.compare_digest(actual,expected)
            except Exception: valid=False
            if not valid:return self.sendj({'error':'رمز مدیر نادرست است.'},403)
            tok=secrets.token_urlsafe(32); SESSIONS[tok]={'role':'admin','customer_id':None,'name':'مدیر Vexta'}; return self.sendj({'token':tok,'role':'admin'})
        if path=='/api/auth/customer':
            phone=re.sub(r'\D','',str(d.get('phone','')))
            if len(phone)<10:return self.sendj({'error':'شماره موبایل معتبر وارد کن.'},400)
            c=ensure_customer(phone,str(d.get('name','')).strip(),str(d.get('referral_code','')))
            if c['data'].get('status') in ['مسدود','غیرفعال']:return self.sendj({'error':'دسترسی این حساب غیرفعال است.'},403)
            # One account per browser-install identifier, and one identifier per account.
            device_id=str(d.get('device_id','')).strip()
            if not re.fullmatch(r'[A-Za-z0-9_-]{20,100}',device_id):return self.sendj({'error':'شناسه دستگاه معتبر نیست. صفحه را تازه‌سازی و دوباره تلاش کن.'},400)
            info=d.get('device_info') if isinstance(d.get('device_info'),dict) else {}
            existing=next((x for x in rows('devices') if x['data'].get('device_id')==device_id and x['data'].get('status')=='متصل'),None)
            owned=next((x for x in rows('devices',str(c['id'])) if x['data'].get('status')=='متصل'),None)
            if existing and str(existing.get('owner'))!=str(c['id']):
                prev=get('customers',int(existing['owner'])) if str(existing.get('owner','')).isdigit() else None
                violation={'device_id':device_id,'device_name':info.get('label','دستگاه ثبت‌شده'),'device_type':info.get('device_type','نامشخص'),'previous_customer_id':existing.get('owner'),'previous_customer':(prev or {}).get('data',{}).get('name','مشتری قبلی'),'target_customer_id':c['id'],'target_customer':c['data'].get('name'),'target_phone':phone,'time':iso(),'reason':'تلاش برای اتصال دستگاه متعلق به حساب دیگر','result':'رد شد'}
                add('device_violations',violation,str(c['id']));add('security_events',violation,str(c['id']))
                return self.sendj({'error':'این دستگاه قبلاً به حساب دیگری متصل شده است. برای انتقال آن، درخواست تعویض دستگاه ثبت کن.'},409)
            if owned and owned['data'].get('device_id')!=device_id:
                v={'device_id':device_id,'previous_device_id':owned['data'].get('device_id'),'previous_customer_id':c['id'],'previous_customer':c['data'].get('name'),'target_customer_id':c['id'],'target_customer':c['data'].get('name'),'target_phone':phone,'time':iso(),'reason':'تلاش حساب برای ورود از دستگاه دوم','result':'رد شد'}
                add('device_violations',v,str(c['id']));add('security_events',v,str(c['id']))
                return self.sendj({'error':'این حساب قبلاً به دستگاه دیگری متصل شده است. ابتدا درخواست تعویض دستگاه ثبت کن.'},409)
            if not existing and not owned:
                ua=self.headers.get('User-Agent',''); info.update({'user_agent':ua,'last_seen':iso(),'login_count':1,'status':'متصل','device_id':device_id,'customer_name':c['data'].get('name'),'phone':phone,'detection_source':info.get('detection_source','تشخیص مرورگر'),'confidence':info.get('confidence','متوسط')})
                add('devices',info,str(c['id']))
            else:
                rec=existing or owned; rd=rec['data']; rd.update(info);rd.update({'device_id':device_id,'customer_name':c['data'].get('name'),'phone':phone,'last_seen':iso(),'login_count':int(rd.get('login_count',0))+1,'status':'متصل'});update('devices',rec['id'],rd)
            tok=secrets.token_urlsafe(32); SESSIONS[tok]={'role':'customer','customer_id':c['id'],'name':c['data'].get('name','مشتری'),'device_id':device_id}; return self.sendj({'token':tok,'role':'customer','customer':c})
        s=self.require()
        if not s:return
        if path=='/api/logout': SESSIONS.pop(self.headers.get('X-Vexta-Session',''),None); return self.sendj({'ok':True})
        if path=='/api/notifications/read' and s['role']=='customer':
            owner=str(s['customer_id'])
            notif_id=int(d.get('id',0) or 0); changed=0
            for n in rows('notifications',owner):
                if notif_id and n['id']!=notif_id: continue
                nd=n['data']; nd['read']=True
                if update('notifications',n['id'],nd): changed+=1
            return self.sendj({'ok':True,'updated':changed})
        if s['role']=='customer':
            cid=str(s['customer_id']); customer=get('customers',s['customer_id']); cd=customer['data']
            if path=='/api/customer/device-change':
                reason=str(d.get('reason','')).strip()
                if len(reason)<5:return self.sendj({'error':'دلیل درخواست را حداقل در ۵ نویسه بنویس.'},400)
                pending=next((x for x in rows('device_change_requests',cid) if x['data'].get('status')=='در انتظار بررسی'),None)
                if pending:return self.sendj({'error':'یک درخواست تعویض دستگاه در انتظار بررسی داری.'},409)
                dev=next((x for x in rows('devices',cid) if x['data'].get('status')=='متصل'),None)
                rid=add('device_change_requests',{'customer_id':int(cid),'customer':cd.get('name'),'phone':cd.get('phone'),'old_device':(dev or {}).get('data',{}),'reason':reason,'status':'در انتظار بررسی','created_at':iso()},cid)
                return self.sendj(get('device_change_requests',rid),201)
            if path=='/api/customer/delete-account':
                if d.get('confirm') is not True or d.get('confirmation_phrase')!='حذف حساب':return self.sendj({'error':'تأیید نهایی حذف حساب معتبر نیست.'},400)
                # Preserve accounting/audit records; void customer assets and subscriptions atomically.
                with LOCK:
                    con=db()
                    try:
                        con.execute('BEGIN IMMEDIATE'); row=con.execute("SELECT * FROM records WHERE entity='customers' AND id=?",(int(cid),)).fetchone()
                        if not row:con.rollback();return self.sendj({'ok':True})
                        customer_data=json.loads(row['data']);old_tokens=int(customer_data.get('tokens',0) or 0);old_wallet=int(customer_data.get('wallet',0) or 0);deleted_at=iso()
                        customer_data.update({'wallet':0,'tokens':0,'status':'حذف‌شده','deleted_at':deleted_at,'name':'حساب حذف‌شده'})
                        con.execute('UPDATE records SET data=?,updated_at=? WHERE id=?',(json.dumps(customer_data,ensure_ascii=False),deleted_at,int(cid)))
                        if old_tokens:
                            tx={'customer_id':int(cid),'delta':-old_tokens,'balance_after':0,'reason':'ابطال موجودی هنگام حذف حساب','reference':'account-delete-token:'+str(cid),'time':deleted_at}
                            con.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',('token_transactions',cid,json.dumps(tx,ensure_ascii=False),deleted_at,deleted_at))
                        if old_wallet:
                            tx={'customer_id':int(cid),'delta':-old_wallet,'balance_after':0,'reason':'ابطال کیف پول هنگام حذف حساب','reference':'account-delete-wallet:'+str(cid),'time':deleted_at}
                            con.execute('INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)',('money_transactions',cid,json.dumps(tx,ensure_ascii=False),deleted_at,deleted_at))
                        subs=con.execute("SELECT id,data FROM records WHERE entity='subscriptions' AND owner=?",(cid,)).fetchall()
                        for sr in subs:
                            sd=json.loads(sr['data']);sd['status']='باطل‌شده';sd['revoked_reason']='حذف حساب مشتری';con.execute('UPDATE records SET data=?,updated_at=? WHERE id=?',(json.dumps(sd,ensure_ascii=False),iso(),sr['id']))
                        devs=con.execute("SELECT id,data FROM records WHERE entity='devices' AND owner=?",(cid,)).fetchall()
                        for dr in devs:
                            dd=json.loads(dr['data']);dd['status']='آزادشده';dd['released_at']=iso();con.execute('UPDATE records SET data=?,updated_at=? WHERE id=?',(json.dumps(dd,ensure_ascii=False),iso(),dr['id']))
                        con.execute("INSERT INTO records(entity,owner,data,created_at,updated_at) VALUES(?,?,?,?,?)",('security_events',cid,json.dumps({'event':'customer_account_deleted','customer_id':int(cid),'phone':customer_data.get('phone'),'time':iso(),'wallet_burned':True,'tokens_burned':True},ensure_ascii=False),iso(),iso()))
                        con.commit()
                    except Exception:con.rollback();raise
                    finally:con.close()
                for key,val in list(SESSIONS.items()):
                    if val.get('role')=='customer' and str(val.get('customer_id'))==cid:SESSIONS.pop(key,None)
                return self.sendj({'ok':True,'message':'حساب حذف و دارایی‌ها باطل شد.'})
            if path=='/api/customer/order':
                product=get('products',int(d.get('product_id',0)))
                if not product or product['data'].get('status')!='فعال':return self.sendj({'error':'این پکیج در دسترس نیست.'},400)
                method=d.get('method','کارت‌به‌کارت')
                if method not in ('کارت‌به‌کارت','نقدی'):return self.sendj({'error':'روش پرداخت معتبر نیست.'},400)
                base_amount=int(product['data'].get('price',0)); amount=base_amount; discount_label=''
                code=str(d.get('discount_code','')).strip().upper()
                if code:
                    discount=next((x for x in rows('discounts') if str(x['data'].get('code','')).upper()==code and x['data'].get('status')=='فعال' and x.get('owner') in (None,cid)),None)
                    if not discount:return self.sendj({'error':'کد تخفیف معتبر یا فعال نیست.'},400)
                    dd=discount['data']; used=int(dd.get('used',0)); limit=int(dd.get('limit',0) or 0); used_by=[str(x) for x in dd.get('used_by',[])]
                    if cid in used_by:return self.sendj({'error':'این کد تخفیف را قبلاً استفاده کرده‌ای.'},409)
                    if limit and used>=limit:return self.sendj({'error':'ظرفیت استفاده از این کد تمام شده است.'},400)
                    expiry=str(dd.get('expires_at','')).strip()
                    if expiry:
                        try:
                            expiry_dt=datetime.fromisoformat(expiry+'T23:59:59+00:00' if len(expiry)==10 else expiry.replace('Z','+00:00'))
                            if expiry_dt.tzinfo is None: expiry_dt=expiry_dt.replace(tzinfo=timezone.utc)
                            if expiry_dt<now():return self.sendj({'error':'مهلت استفاده از این کد تخفیف تمام شده است.'},400)
                        except ValueError:return self.sendj({'error':'تاریخ انقضای کد تخفیف نامعتبر است.'},400)
                    value=max(0,min(100,int(dd.get('value',0)))) if dd.get('kind')=='درصدی' else max(0,int(dd.get('value',0)))
                    amount=max(0,base_amount-(base_amount*value//100 if dd.get('kind')=='درصدی' else value));dd['used']=used+1;dd['used_by']=used_by+[cid];update('discounts',discount['id'],dd);discount_label=code
                due=now()+timedelta(days=5)
                code='VXT-'+secrets.token_hex(3).upper()
                status='در انتظار پرداخت' if method!='نقدی' else 'در انتظار پرداخت'
                oid=add('orders',{'code':code,'customer_id':s['customer_id'],'customer':cd.get('name'),'product_id':product['id'],'product':product['data'].get('name'),'amount':amount,'base_amount':base_amount,'discount':discount_label,'method':method,'status':status,'created_at':iso(),'due_at':due.isoformat(timespec='seconds'),'due_days':5},cid)
                notify('admin','سفارش جدید',f"سفارش {code} ثبت شد.",'info'); log(cd.get('name'),'ثبت سفارش',code)
                return self.sendj({'id':oid,'code':code,'due_at':due.isoformat()},201)
            if path=='/api/customer/receipt':
                oid=int(d.get('order_id',0)); order=get('orders',oid)
                if not order or str(order['data'].get('customer_id'))!=cid:return self.sendj({'error':'سفارش پیدا نشد.'},404)
                if order['data'].get('status') not in ('در انتظار پرداخت','در انتظار بررسی'):return self.sendj({'error':'برای این سفارش امکان ارسال فیش وجود ندارد.'},409)
                filedata=str(d.get('file_data','')); filename=str(d.get('filename','فیش پرداخت'))[:120]
                if filedata and not filedata.startswith('data:image/') and not filedata.startswith('data:application/pdf;'):return self.sendj({'error':'فرمت فیش باید تصویر یا PDF باشد.'},400)
                rid=add('receipts',{'order_id':oid,'order_code':order['data'].get('code',''),'request_type':'خرید اشتراک','customer_id':s['customer_id'],'customer':cd.get('name'),'phone':cd.get('phone'),'amount':order['data'].get('amount'),'filename':filename,'file_data':filedata,'sent_at':iso(),'status':'در انتظار بررسی'},cid)
                od=order['data'];od['status']='در انتظار بررسی';od['receipt_id']=rid;update('orders',oid,od)
                notify('admin','فیش پرداخت جدید',f"فیش {cd.get('name')} برای سفارش {od.get('code')} ارسال شد.",'warning')
                return self.sendj({'id':rid,'status':'در انتظار بررسی'},201)
            if path=='/api/customer/invite':
                phone=re.sub(r'\D','',str(d.get('phone','')))
                if len(phone)<10:return self.sendj({'error':'شماره موبایل دوست معتبر نیست.'},400)
                if phone==cd.get('phone'):return self.sendj({'error':'نمی‌توانی خودت را دعوت کنی.'},400)
                prior=next((x for x in rows('referrals',cid) if x['data'].get('friend_phone')==phone),None)
                if prior:return self.sendj({'error':'برای این شماره قبلاً دعوت ثبت شده است.'},409)
                rid=add('referrals',{'inviter_id':s['customer_id'],'inviter':cd.get('name'),'friend_phone':phone,'code':cd.get('referral_code'),'status':'دعوت‌شده','created_at':iso()},cid)
                return self.sendj({'id':rid,'code':cd.get('referral_code')},201)
            if path=='/api/customer/wallet-request':
                typ=d.get('type','شارژ')
                if typ not in ('شارژ','برداشت'):return self.sendj({'error':'نوع درخواست معتبر نیست.'},400)
                amount=int(d.get('amount',0))
                if amount<=0:return self.sendj({'error':'مبلغ معتبر وارد کن.'},400)
                if typ=='برداشت':
                    reserved=sum(int(x['data'].get('amount',0)) for x in rows('wallet',cid) if x['data'].get('type')=='برداشت' and x['data'].get('status')=='در انتظار بررسی')
                    if amount>int(cd.get('wallet',0))-reserved:return self.sendj({'error':'موجودی آزاد کیف پول پس از کسر برداشت‌های در انتظار کافی نیست.'},400)
                receipt=str(d.get('receipt_file_data','') or '')
                filename=str(d.get('receipt_filename','') or '')[:160]
                if typ=='شارژ' and receipt:
                    if not (receipt.startswith('data:image/') or receipt.startswith('data:application/pdf;')):
                        return self.sendj({'error':'رسید باید تصویر یا PDF باشد.'},400)
                    if len(receipt)>12*1024*1024:
                        return self.sendj({'error':'حجم رسید بیش از حد مجاز است.'},413)
                elif typ=='برداشت' and receipt:
                    return self.sendj({'error':'برای درخواست برداشت نیازی به رسید پرداخت نیست.'},400)
                request_code='WAL-'+now().strftime('%y%m%d')+'-'+secrets.token_hex(3).upper()
                rid=add('wallet',{'request_code':request_code,'request_type':'شارژ کیف پول' if typ=='شارژ' else 'برداشت کیف پول','customer_id':s['customer_id'],'customer':cd.get('name'),'phone':cd.get('phone'),'type':typ,'amount':amount,'status':'در انتظار بررسی','note':str(d.get('note','')),'created_at':iso(),'reserved':typ=='برداشت','receipt_file_data':receipt,'receipt_filename':filename},cid)
                notify('admin','درخواست کیف پول',f"درخواست {typ} از {cd.get('name')}",'warning');return self.sendj({'id':rid},201)
            return self.sendj({'error':'مسیر نامعتبر'},404)
        # Admin file distribution and spreadsheet import
        if s['role']=='admin' and path.startswith('/api/admin/settle-cash/'):
            try:
                oid=int(path.rsplit('/',1)[-1]); order=get('orders',oid)
                if not order or order['data'].get('method')!='نقدی':return self.sendj({'error':'سفارش نقدی پیدا نشد.'},404)
                od=order['data']
                if od.get('status')!='فعال - پرداخت‌نشده':return self.sendj({'error':'این سفارش در وضعیت پرداخت‌نشده نقدی نیست.'},409)
                od['status']='تأیید شده';od['paid_at']=iso();od['cash_received_at']=iso();update('orders',oid,od)
                for sub in rows('subscriptions',str(od.get('customer_id'))):
                    if int(sub['data'].get('order_id',0))==oid and sub['data'].get('payment_status')=='پرداخت‌نشده':
                        sd=sub['data'];sd['payment_status']='پرداخت‌شده';sd['status']='فعال';update('subscriptions',sub['id'],sd);break
                notify(od.get('customer_id'),'پرداخت نقدی ثبت شد','پرداخت نقدی سفارش شما توسط مدیریت ثبت شد.','success')
                return self.sendj({'ok':True})
            except Exception as e:return self.sendj({'error':str(e)},400)
        if s['role']=='admin' and path.startswith('/api/admin/subscription/revoke/'):
            try:
                sid=int(path.rsplit('/',1)[-1]); rec=get('subscriptions',sid)
                if not rec:return self.sendj({'error':'اشتراک پیدا نشد.'},404)
                sd=rec['data']
                if sd.get('status')=='باطل‌شده':return self.sendj({'error':'این اشتراک قبلاً باطل شده است.'},409)
                sd.update({'status':'باطل‌شده','revoked_at':iso(),'revoke_reason':str(d.get('reason','درخواست مدیر'))})
                update('subscriptions',sid,sd); notify(sd.get('customer_id'),'ابطال اشتراک','اشتراک '+str(sd.get('product',''))+' باطل شد. دلیل: '+sd['revoke_reason'],'warning')
                return self.sendj({'ok':True})
            except Exception as e:return self.sendj({'error':str(e)},400)
        if s['role']=='admin' and path=='/api/admin/publish-file':
            try:
                name=str(d.get('filename','file'))[:160]; raw=str(d.get('file_data',''))
                if ',' in raw: raw=raw.split(',',1)[1]
                blob=base64.b64decode(raw,validate=True); content_hash=hashlib.sha256(blob).hexdigest()
                if len(blob)>30*1024*1024:return self.sendj({'error':'حداکثر حجم فایل ۳۰ مگابایت است.'},413)
                ext=Path(name).suffix.lower(); fid=uuid.uuid4().hex
                UPLOADS.mkdir(exist_ok=True)
                if ext=='.zip':
                    dest=UPLOADS/'published'/fid; entry=safe_extract_zip(blob,dest)
                    rel=(entry/'index.html').relative_to(ROOT).as_posix(); launch='/'+rel
                    ftype='HTML'
                elif ext=='.pdf':
                    dest=UPLOADS/'published'/fid; dest.mkdir(parents=True,exist_ok=True); target=dest/(Path(name).name or 'document.pdf'); target.write_bytes(blob); launch='/uploads/published/'+fid+'/'+quote(target.name); ftype='PDF'
                elif ext in ('.html','.htm'):
                    dest=UPLOADS/'published'/fid; dest.mkdir(parents=True,exist_ok=True); target=dest/(Path(name).name or 'index.html'); target.write_bytes(blob); launch='/uploads/published/'+fid+'/'+quote(target.name); ftype='HTML'
                else:return self.sendj({'error':'فقط PDF، HTML و ZIP پشتیبانی می‌شوند.'},400)
                selected=[int(x) for x in d.get('product_ids',[])]; requested_difficulty=str(d.get('difficulty','auto')); analysis=analyze_learning_file(blob,name,ext); difficulty=analysis['difficulty'] if requested_difficulty=='auto' else requested_difficulty; rates=d.get('rates',{})
                if not selected:return self.sendj({'error':'حداقل یک اشتراک مقصد انتخاب کن.'},400)
                eligible=[]
                for sub in rows('subscriptions'):
                    sd=sub['data']
                    if sd.get('status') not in ('فعال','فعال - پرداخت‌نشده') or int(sd.get('product_id',0)) not in selected: continue
                    try:
                        if sd.get('end_at') and datetime.fromisoformat(sd['end_at'])<=now():continue
                    except:pass
                    cid=int(sd.get('customer_id',0)); customer=get('customers',cid)
                    if customer and customer['data'].get('status')=='فعال': eligible.append(cid)
                # The publication is a single immutable package; one assignment and one token debit per customer.
                cost_by_product={int(k):max(0,int(v)) for k,v in rates.items() if str(k).isdigit()}
                level_key={'آسان':'easy','متوسط':'medium','سخت':'hard','بسیار سخت':'very_hard'}[difficulty]
                if requested_difficulty=='auto':
                    for product in rows('products'):
                        if product['id'] in selected:cost_by_product[product['id']]=max(0,int(product['data'].get('token_'+level_key,0)))
                assigned=0; skipped=0; already=0
                for cid in sorted(set(eligible)):
                    active_subs=[x for x in rows('subscriptions',str(cid)) if x['data'].get('status') in ('فعال','فعال - پرداخت‌نشده') and int(x['data'].get('product_id',0)) in selected]
                    product_id=int(active_subs[0]['data'].get('product_id',0)) if active_subs else 0
                    cost=cost_by_product.get(product_id,0)
                    if any(x['data'].get('content_hash')==content_hash for x in rows('files',str(cid))): already+=1; continue
                    file_record={'content_hash':content_hash,'file_id':fid,'name':name,'type':ftype,'description':str(d.get('description','')),'difficulty':difficulty,'product_id':product_id,'launch_url':launch,'published_at':iso()}
                    if cost:
                        ok,_=atomic_publish_assignment(cid,cost,'انتشار فایل: '+name,'publish:'+content_hash+':'+str(cid),file_record)
                    else:
                        add('files',dict(file_record,token_cost=0),str(cid));ok=True
                    if not ok: skipped+=1; continue
                    notify(cid,'فایل جدید برای اشتراک شما',f'فایل «{name}» به بخش فایل‌ها اضافه شد.','success'); assigned+=1
                # Admin copy/metadata for future audit and re-publishing policy; no customer data is fabricated.
                add('files',{'file_id':fid,'name':name,'type':ftype,'description':str(d.get('description','')),'difficulty':difficulty,'launch_url':launch,'product_ids':selected,'rates':cost_by_product,'published_at':iso(),'content_hash':content_hash,'assigned_count':assigned,'skipped_insufficient_tokens':skipped,'already_assigned':already},'admin')
                return self.sendj({'ok':True,'file_id':fid,'assigned':assigned,'skipped':skipped,'already':already,'analysis':analysis|{'difficulty':difficulty,'selected_mode':requested_difficulty}},201)
            except Exception as e:return self.sendj({'error':'انتشار کامل نشد: '+str(e)},400)
        # Admin operations
        if s['role']=='admin':
            m=re.match(r'^/api/admin/review/(orders|wallet|receipts)/(\d+)$',path)
            if m:
                entity,rid=m.group(1),int(m.group(2)); rec=get(entity,rid)
                if not rec:return self.sendj({'error':'مورد پیدا نشد.'},404)
                decision=d.get('decision'); reason=str(d.get('reason',''))
                if decision not in ['approve','reject']:return self.sendj({'error':'تصمیم نامعتبر'},400)
                rd=rec['data']; approved=decision=='approve'
                if entity=='receipts':
                    if rd.get('status') in ('تأییدشده','ردشده'):return self.sendj({'error':'این فیش قبلاً بررسی شده است.'},409)
                    rd['status']='تأییدشده' if approved else 'ردشده';rd['reviewed_at']=iso();rd['review_reason']=reason
                    if approved: rd['file_data']=''
                    update(entity,rid,rd)
                    order=get('orders',int(rd['order_id']))
                    if order:
                        od=order['data'];od['status']='تأیید شده' if approved else 'رد شده';od['paid_at']=iso() if approved else None;update('orders',order['id'],od)
                        if approved:
                            cust=get('customers',int(rd['customer_id']));cd=cust['data'];prod=get('products',int(od.get('product_id',0)))
                            if prod:
                                pd=prod['data']; sub={'order_id':order['id'],'customer':cd.get('name'),'product_id':prod['id'],'product':pd.get('name'),'status':'فعال','payment_status':'پرداخت‌شده','start_at':iso(),'end_at':(now()+timedelta(days=int(pd.get('duration_days',30)))).isoformat(timespec='seconds'),'tokens':int(pd.get('tokens',0))}
                                atomic_purchase_subscription(cust['id'],int(pd.get('tokens',0)),'خرید اشتراک '+str(pd.get('name')),'order:'+str(order['id']),sub)
                        notify(rd['customer_id'],'نتیجه بررسی فیش','فیش پرداخت شما '+('تأیید شد.' if approved else 'رد شد: '+reason),'success' if approved else 'danger')
                elif entity=='orders':
                    if rd.get('status') in ('تأیید شده','رد شده'):return self.sendj({'error':'این سفارش قبلاً بررسی شده است.'},409)
                    if approved and rd.get('method')!='نقدی':return self.sendj({'error':'برای پرداخت کارت‌به‌کارت، فیش را در بخش فیش‌های پرداختی بررسی کن.'},400)
                    rd['status']=('فعال - پرداخت‌نشده' if rd.get('method')=='نقدی' else 'تأیید شده') if approved else 'رد شده';rd['reviewed_at']=iso();rd['review_reason']=reason
                    if approved and rd.get('method')!='نقدی':rd['paid_at']=iso()
                    update(entity,rid,rd)
                    if approved:
                        cust=get('customers',int(rd.get('customer_id',0)));prod=get('products',int(rd.get('product_id',0)))
                        if cust and prod:
                            cd=cust['data'];pd=prod['data'];sub={'order_id':rid,'customer':cd.get('name'),'product_id':prod['id'],'product':pd.get('name'),'status':'فعال - پرداخت‌نشده' if rd.get('method')=='نقدی' else 'فعال','payment_status':'پرداخت‌نشده' if rd.get('method')=='نقدی' else 'پرداخت‌شده','start_at':iso(),'end_at':(now()+timedelta(days=int(pd.get('duration_days',30)))).isoformat(timespec='seconds'),'tokens':int(pd.get('tokens',0))};atomic_purchase_subscription(cust['id'],int(pd.get('tokens',0)),'خرید اشتراک '+str(pd.get('name')),'order:'+str(rid),sub)
                    notify(rd.get('customer_id'),'نتیجه سفارش','سفارش شما '+('تأیید شد.' if approved else 'رد شد: '+reason),'success' if approved else 'danger')
                else:
                    ok,result=atomic_review_wallet_request(rid,approved,reason)
                    if not ok:return self.sendj({'error':'درخواست قبلاً بررسی شده یا موجودی کیف پول کافی نیست.'},409)
                    notify(result,'نتیجه درخواست کیف پول','درخواست '+str(rd.get('type'))+' شما '+('تأیید شد.' if approved else 'رد شد: '+reason),'success' if approved else 'danger')
                    return self.sendj({'ok':True})
                log('مدیر','بررسی '+entity, f"#{rid}: {decision} {reason}");return self.sendj({'ok':True})
            if path.startswith('/api/admin/device-change/approve/') or path.startswith('/api/admin/device-change/reject/'):
                m=re.match(r'^/api/admin/device-change/(approve|reject)/(\d+)$',path)
                if not m:return self.sendj({'error':'درخواست نامعتبر است.'},404)
                req=get('device_change_requests',int(m.group(2)))
                if not req or req['data'].get('status')!='در انتظار بررسی':return self.sendj({'error':'درخواست پیدا نشد یا قبلاً بررسی شده است.'},409)
                rd=req['data'];cid=str(rd.get('customer_id'));decision=m.group(1)
                if decision=='approve':
                    for dv in rows('devices',cid):
                        if dv['data'].get('status')=='متصل':
                            dd=dv['data'];dd['status']='آزادشده';dd['released_at']=iso();update('devices',dv['id'],dd)
                    rd['status']='تأیید شد';rd['reviewed_at']=iso()
                else:rd['status']='رد شد';rd['reviewed_at']=iso();rd['review_reason']=str(d.get('reason',''))
                update('device_change_requests',req['id'],rd);notify(cid,'نتیجه درخواست تعویض دستگاه','درخواست تعویض دستگاه شما '+('تأیید شد؛ اکنون می‌توانی با دستگاه جدید وارد شوی.' if decision=='approve' else 'رد شد.') ,'success' if decision=='approve' else 'warning')
                return self.sendj({'ok':True})
            m=re.match(r'^/api/admin/data/([a-z]+)/?(\d*)$',path)
            if m:
                e=m.group(1); rid=m.group(2)
                if e not in ENTITIES:return self.sendj({'error':'بخش نامعتبر'},404)
                if e=='discounts':
                    code=str(d.get('code','')).strip().upper()
                    if not re.fullmatch(r'[A-Z0-9_-]{3,40}',code):return self.sendj({'error':'کد تخفیف باید ۳ تا ۴۰ نویسه و فقط شامل حروف انگلیسی، عدد، خط تیره یا زیرخط باشد.'},400)
                    if any(str(x['data'].get('code','')).upper()==code for x in rows('discounts')):return self.sendj({'error':'این کد تخفیف قبلاً ثبت شده است.'},409)
                    kind=d.get('kind','درصدی'); value=int(d.get('value',0) or 0)
                    if kind not in ('درصدی','مبلغ ثابت') or value<=0 or (kind=='درصدی' and value>100):return self.sendj({'error':'مقدار یا نوع تخفیف معتبر نیست.'},400)
                    d['code']=code; d.setdefault('used',0); d.setdefault('used_by',[]); d.setdefault('description','')
                if not rid:
                    data=d; owner=None
                    if e=='customers':
                        initial_tokens=int(data.get('tokens',0));initial_wallet=int(data.get('wallet',0));data['tokens']=0;data['wallet']=0;data.setdefault('debt',0)
                    else:initial_tokens=initial_wallet=0
                    if e=='subscriptions' and data.get('customer_id'): owner=str(data.get('customer_id'))
                    new=add(e,data,owner)
                    if e=='customers':
                        if initial_tokens:atomic_token_change(new,initial_tokens,'موجودی اولیه توسط مدیر','customer-init-token:'+str(new))
                        if initial_wallet:atomic_wallet_change(new,initial_wallet,'موجودی اولیه توسط مدیر','customer-init-wallet:'+str(new))
                    log('مدیر','ایجاد '+e,str(new));return self.sendj(get(e,new),201)
                rid=int(rid);old=get(e,rid)
                if not old:return self.sendj({'error':'مورد پیدا نشد'},404)
                if not update(e,rid,d):return self.sendj({'error':'ذخیره نشد'},500)
                log('مدیر','ویرایش '+e,'#'+str(rid));return self.sendj({'ok':True})
        return self.sendj({'error':'مسیر نامعتبر'},404)
    def do_PUT(self):
        p=urlparse(self.path);s=self.require('admin')
        if not s:return
        try:d=self.body()
        except Exception as e:return self.sendj({'error':str(e)},400)
        m=re.match(r'^/api/admin/data/([a-z]+)/?(\d+)$',p.path)
        if not m:return self.sendj({'error':'مسیر نامعتبر'},404)
        e,rid=m.group(1),int(m.group(2))
        if e not in ENTITIES:return self.sendj({'error':'بخش نامعتبر'},404)
        if e=='discounts':
            old_discount=get('discounts',rid)
            if not old_discount:return self.sendj({'error':'کد تخفیف پیدا نشد.'},404)
            code=str(d.get('code',old_discount['data'].get('code',''))).strip().upper()
            if not re.fullmatch(r'[A-Z0-9_-]{3,40}',code):return self.sendj({'error':'کد تخفیف نامعتبر است.'},400)
            if any(x['id']!=rid and str(x['data'].get('code','')).upper()==code for x in rows('discounts')):return self.sendj({'error':'این کد تخفیف قبلاً ثبت شده است.'},409)
            kind=d.get('kind',old_discount['data'].get('kind','درصدی')); value=int(d.get('value',old_discount['data'].get('value',0)) or 0)
            if kind not in ('درصدی','مبلغ ثابت') or value<=0 or (kind=='درصدی' and value>100):return self.sendj({'error':'مقدار یا نوع تخفیف معتبر نیست.'},400)
            d['code']=code; d.setdefault('used',old_discount['data'].get('used',0)); d.setdefault('used_by',old_discount['data'].get('used_by',[]))
        if e=='customers':
            old=get('customers',rid)
            if not old:return self.sendj({'error':'مشتری پیدا نشد.'},404)
            try:
                token_delta=int(d.get('tokens',old['data'].get('tokens',0)))-int(old['data'].get('tokens',0))
                wallet_delta=int(d.get('wallet',old['data'].get('wallet',0)))-int(old['data'].get('wallet',0))
                ok,_=atomic_customer_adjustment(rid,token_delta,wallet_delta,'اصلاح موجودی توسط مدیر',uuid.uuid4().hex)
                if not ok:return self.sendj({'error':'موجودی توکن یا کیف پول کافی نیست.'},400)
            except Exception as ex:return self.sendj({'error':'تغییر موجودی ثبت نشد: '+str(ex)},400)
        if not update(e,rid,d):return self.sendj({'error':'مورد پیدا نشد'},404)
        log('مدیر','ویرایش '+e,'#'+str(rid));return self.sendj({'ok':True})
    def do_DELETE(self):
        p=urlparse(self.path);s=self.require('admin')
        if not s:return
        m=re.match(r'^/api/admin/data/([a-z]+)/?(\d+)$',p.path)
        if not m:return self.sendj({'error':'مسیر نامعتبر'},404)
        e,rid=m.group(1),int(m.group(2))
        if e not in ENTITIES:return self.sendj({'error':'بخش نامعتبر'},404)
        c=db();cur=c.execute('DELETE FROM records WHERE id=? AND entity=?',(rid,e));ok=cur.rowcount>0;c.commit();c.close();log('مدیر','حذف '+e,'#'+str(rid));return self.sendj({'ok':ok})

if __name__=='__main__':
    (ROOT/'data').mkdir(exist_ok=True);UPLOADS.mkdir(exist_ok=True)
    init_db(); UPLOADS.mkdir(exist_ok=True); cleanup_expired_uploads(); threading.Thread(target=scheduler,daemon=True).start()
    # Railway (and similar hosts) injects the public listening port through PORT.
    # Bind to 0.0.0.0 so the platform's proxy can reach this process.
    host = os.environ.get('HOST', '0.0.0.0')
    port = int(os.environ.get('PORT', '8766'))
    print(f'Vexta server listening on {host}:{port}', flush=True)
    ThreadingHTTPServer((host, port), Handler).serve_forever()
