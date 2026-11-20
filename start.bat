@echo off
cd /d "%~dp0"
where py >nul 2>nul
if %errorlevel%==0 (start "Vexta Local" py -3 server.py) else (start "Vexta Local" python server.py)
timeout /t 2 >nul
start http://127.0.0.1:8766
