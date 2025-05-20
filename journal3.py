#python start3.py --mt5-login 61339636 --mt5-password "Neema@#54" --mt5-server "Pepperstone-Demo" --symbols XAUUSD EURUSD US500 NAS100 USDJPY --timeframes M1 M5 M15 M30 H1 H4  --lot-size 0.2 --daily-max-profit 1000  --risk-percent 1.5
#python start3.py --mt5-login 61339636 --mt5-password "Neema@#54" --mt5-server "Pepperstone-Demo" --symbols XAUUSD --timeframes M1 M5 --lot-size 0.2 --daily-max-profit 1000  --risk-percent 1.5
import os
import sys
import time
import shutil
import json
import queue
import random
import logging
import warnings
import threading
import argparse
import subprocess
import MetaTrader5 as mt5
from datetime import datetime, timedelta
import pandas as pd
import numpy as np
import plotly.graph_objects as go
import re
import requests
import keyboard
import colorlog
import talib
import psutil
import atexit
from reportlab.lib import colors
from reportlab.lib.pagesizes import letter
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Image, Table, TableStyle
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from prompt_toolkit import PromptSession
from prompt_toolkit.completion import WordCompleter
from prompt_toolkit.history import InMemoryHistory
from concurrent.futures import ThreadPoolExecutor
import tempfile
import shutil
from tqdm import tqdm

warnings.filterwarnings("ignore", category=UserWarning, message="Pandas doesn't allow columns to be created via a new attribute name")

class TradingStrategy:
    def __init__(self, mt5_login=None, mt5_password=None, mt5_server=None, symbols=None, timeframes=None, lot_size=0.1, daily_max_profit=500, simulate=False, risk_percent=2.0, mt5_path=None):
        # Initialize trading lock state before other attributes
        self.trading_locked = False
        self.trading_lock_reason = ""
        # Setup logging first       
        self._setup_logging()
        self.simulate = False
        # Add drawdown tracking attributes
        self.balance_file = "daily_balance.json"
        self.max_drawdown_percent = 50  # 50% maximum drawdown
        self.initial_balance = None
        self.lowest_balance = None
        self.load_daily_balance()
        self.initialize_daily_balance()
        self.mt5_login = mt5_login or 61318849
        self.mt5_password = mt5_password or "Neema@#54"
        self.mt5_server = mt5_server or "Pepperstone-Demo"
            # Initialize status update thread
        self.status_update_interval = 1  # Update every second
        self.status_thread_running = True
        self.status_thread = threading.Thread(target=self.status_update_loop, daemon=True)
        self.status_thread.start()
        
        # Initialize mock trade manager
        self.mock_trade_manager = MockTradeManager(self)

        # Add market check intervals
        self.market_check_interval = 60  # Check market status every 60 seconds
        self.market_closed_sleep = 300   # Sleep for 5 minutes when market is closed

        self.ADMIN_PASSWORD = "TR@d3L3@d3r2025#"  # Complex password for admin override
        self.max_daily_loss = -500  # Set maximum daily loss in points (negative value)
        # Add lock file path
        self.lock_file = "trading_lock.json"
        # Load lock state from file
        self.load_lock_state()

        # Add report generation folder
        self.reports_folder = "trade_reports"
        os.makedirs(self.reports_folder, exist_ok=True)
        
        # Register Times New Roman font
        pdfmetrics.registerFont(TTFont('Times-Roman', 'times.ttf'))
        self.accounts = {
            'default': {'login': self.mt5_login, 'password': self.mt5_password, 'server': self.mt5_server}
        }
        self.current_account = 'default'
        self.sync_enabled = False

        self.TELEGRAM_BOT_TOKEN = "7135089206:AAEmnAztKDkjXg5jM4dXbrjfF3dCvcwJ9Ow"
        self.TELEGRAM_CHAT_ID = "6178394807"
        self.telegram_offset = 0

        self.symbols = symbols if symbols is not None else ['XAUUSD']

        # Initialize symbol_info dictionary
        self.symbol_info = {symbol: {} for symbol in self.symbols}
        self.point = {symbol: None for symbol in self.symbols}

        # Define timeframe_configs before using it in parse_timeframe
        self.timeframe_configs = {
            'M1': mt5.TIMEFRAME_M1, 'M5': mt5.TIMEFRAME_M5, 'M15': mt5.TIMEFRAME_M15,
            'M30': mt5.TIMEFRAME_M30, 'H1': mt5.TIMEFRAME_H1, 'H4': mt5.TIMEFRAME_H4
        }
        # Now parse timeframes after timeframe_configs is defined
        self.timeframes = [self.parse_timeframe(tf) for tf in (timeframes or ['M1'])]

        self.timeframe_intervals = {
            mt5.TIMEFRAME_M1: 60, mt5.TIMEFRAME_M5: 300, mt5.TIMEFRAME_M15: 900,
            mt5.TIMEFRAME_M30: 1800, mt5.TIMEFRAME_H1: 3600, mt5.TIMEFRAME_H4: 14400
        }

        self.lot_size = lot_size
        self.deviation = 10

        self.lot_size = lot_size
        self.deviation = 10  # Adjusted to match second half
        self.max_retries = 3
        self.retry_delay = 5
        self.simulate = simulate
        self.risk_percent = risk_percent
        self.daily_max_profit = daily_max_profit

        self.primary_strategy_enabled = True
        self.suretrend_automation_enabled = False
        self.grid_trading_enabled = False
        self.grid_automation_enabled = False
        self.momentum_automation_enabled = False  # Removed momentum_enabled, using automation flag only

        self.grid_levels = 5
        self.grid_spacing = 10

        self.ma_configs = {
            tf: {'fast': 3 if tf in [mt5.TIMEFRAME_M1, mt5.TIMEFRAME_M5] else 5,
                 'slow': 8 if tf in [mt5.TIMEFRAME_M1, mt5.TIMEFRAME_M5] else 10,
                 'exit_fast': 5, 'exit_slow': 10}
            for tf in self.timeframes  # Changed to self.timeframes for consistency
        }
        self.macd_fast, self.macd_slow, self.macd_signal = 12, 26, 9
        self.momentum_period = 14
        self.psar_step, self.psar_max = 0.02, 0.2
        self.bollinger_period, self.bollinger_dev = 20, 2
        self.atr_period = 14

        self.breakeven_configs = {tf: 50.0 for tf in self.timeframes}
        self.trailing_stop_configs = {tf: 50.0 for tf in self.timeframes}
        self.trailing_delay_configs = {tf: 50.0 for tf in self.timeframes}
        self.signal_cooldown = 300  # 5 minutes default, matching second half
        self.initial_sl = 200  # Default SL in points, matching second half
        #self.initial_balance = 1000
        self.dynamic_management_enabled = False  # Aligned with second half default
        self.exit_signals_enabled = True
        self.use_m5_exit = False

        self.positions = {symbol: {} for symbol in self.symbols}
        self.daily_profit = {symbol: 0.0 for symbol in self.symbols}
        self.daily_trades = {symbol: [] for symbol in self.symbols}  # Simplified to list per symbol
        self.trade_history = {symbol: [] for symbol in self.symbols}
        self.grid_history = {symbol: [] for symbol in self.symbols}
        self.suretrend_history = {symbol: [] for symbol in self.symbols}
        self.momentum_history = {symbol: [] for symbol in self.symbols}
        self.trading_allowed = {symbol: True for symbol in self.symbols}
        self.last_check_times = {symbol: {tf: datetime.now() for tf in self.timeframes} for symbol in self.symbols}
        self.last_signal_times = {symbol: {tf: datetime.now() - timedelta(seconds=self.signal_cooldown) for tf in self.timeframes} for symbol in self.symbols}
        self.waiting_for_trade_confirmation = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.trade_confirmation_queue = queue.Queue()
        self.command_lock = threading.Lock()
        self.context_symbol = None
        self.threads = []
        self.symbol_terminal_threads = {}

        # Initialize ma_exit_enabled with both string and numeric timeframe keys
        self.ma_exit_enabled = {}
        for symbol in self.symbols:
            self.ma_exit_enabled[symbol] = {}
            for tf in self.timeframes:
                # Add numeric timeframe key
                self.ma_exit_enabled[symbol][tf] = False
                # Add string timeframe key
                tf_name = self.get_timeframe_name(tf)
                self.ma_exit_enabled[symbol][tf_name] = False
                # Special case for M5
                if tf_name == 'M5':
                    self.ma_exit_enabled[symbol][tf_name] = self.use_m5_exit

        self.volatility_check_enabled = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.psar_filter_enabled = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.psar_filter_timeframe = {symbol: {tf: mt5.TIMEFRAME_H1 for tf in self.timeframes} for symbol in self.symbols}
        self.data_cache = {symbol: {tf: {'df': None, 'last_time': None} for tf in self.timeframes} for symbol in self.symbols}
        self.suretrend_conditions_met = {symbol: {tf: {'buy': False, 'sell': False} for tf in self.timeframes} for symbol in self.symbols}
        self.trades_per_strategy = {symbol: {tf: {"primary": 0, "suretrend": 0, "grid": 0, "momentum": 0, "breakout_momentum": 0} for tf in self.timeframes} for symbol in self.symbols}

        self._setup_logging()
        self.load_trade_history()
        atexit.register(self.cleanup)
        keyboard.on_press_key("q", self.handle_exit)

        # Enhanced error handling settings
        self.max_consecutive_errors = 3
        self.error_cooldown = 60  # seconds
        self.last_error_time = None
        self.consecutive_errors = 0
        
        # Load saved Telegram offset
        self.load_telegram_offset()
        
        # Initialize connection status
        self.mt5_connected = False
        self.telegram_connected = False

        # Add semi-automated mode variables
        self.primary_strategy_semi_auto = False
        self.suretrend_semi_auto = False
        self.grid_semi_auto = False
        self.momentum_semi_auto = False

        # Add MT5 path to the initialization
        self.mt5_path = mt5_path or r"C:\Program Files\MetaTrader 5\terminal64.exe"

        # Add new sync-related attributes
        self.sync_interval = 1  # Sync every 1 second
        self.last_sync_time = datetime.now()
        self.last_known_positions = {symbol: {} for symbol in self.symbols}
        self.last_known_history = {symbol: set() for symbol in self.symbols}
        self.external_trade_defaults = {
            'sl_points': 200,  # Default SL in points
            'tp_ratio': 2.0,   # TP = SL * tp_ratio
            'timeframe': mt5.TIMEFRAME_M1  # Default timeframe for external trades
        }
        
        # Start continuous sync thread
        self.sync_thread = threading.Thread(target=self.continuous_sync_loop, daemon=True)
        self.sync_thread.start()

        # Add HFScalper strategy attributes
        self.hfscalper_enabled = False
        self.hfscalper_semi_auto = False
        self.hfscalper_min_momentum = 0.0001
        self.hfscalper_volatility_threshold = 1.5
        self.hfscalper_tp_points = 10
        self.hfscalper_psar_enabled = False
        self.hfscalper_psar_step = 0.02
        self.hfscalper_psar_max = 0.2
        self.hfscalper_history = {symbol: [] for symbol in (symbols or ['XAUUSD'])}

        self.breakout_momentum_enabled = False
        self.breakout_momentum_semi_auto = False
        self.breakout_momentum_history = {symbol: [] for symbol in self.symbols}
        self.rsi_period = 14  # RSI period for overbought/oversold detection
        self.rsi_overbought = 70
        self.rsi_oversold = 30
        self.consolidation_lookback = 20  # Lookback period for consolidation detection
        self.consolidation_threshold = 0.05  # BB width threshold for consolidation
        self.breakout_multiplier = 1.5  # TP multiplier based on consolidation range
        self.atr_multiplier_sl = 1.5  # SL multiplier based on ATR
        self.atr_multiplier_trailing = 1.0  # Trailing stop multiplier

        # Add new signal optimization attributes
        self.signal_optimization_enabled = False
        self.realtime_signals_enabled = True
        self.signal_quality_threshold = 0.7
        self.signal_interval = 1  # seconds
        self.signal_history = {symbol: {tf: [] for tf in self.timeframes} for symbol in self.symbols}
        self.signal_performance = {symbol: {tf: {'total': 0, 'successful': 0} for tf in self.timeframes} for symbol in self.symbols}
        self.signal_alerts_enabled = True
        self.signal_logging_enabled = True
        self.signal_filters = {
            'momentum_threshold': 0.0001,
            'volatility_threshold': 1.5,
            'min_confirmation_signals': 2,
            'min_signal_quality': 0.7
        }
        
        self.strategy_performance = {
            'primary': {'total': 0, 'successful': 0, 'profit': 0.0},
            'suretrend': {'total': 0, 'successful': 0, 'profit': 0.0},
            'grid': {'total': 0, 'successful': 0, 'profit': 0.0},
            'momentum': {'total': 0, 'successful': 0, 'profit': 0.0},
            'hfscalper': {'total': 0, 'successful': 0, 'profit': 0.0},
            'breakout_momentum': {'total': 0, 'successful': 0, 'profit': 0.0}
        }
        
        # Signal quality metrics
        self.signal_quality_metrics = {
            'accuracy': 0.0,
            'profit_factor': 0.0,
            'win_rate': 0.0,
            'avg_profit': 0.0,
            'avg_loss': 0.0
        }

        # Add SureTrend tracking attributes
        self.suretrend_tracking = {
            symbol: {
                tf: {
                    'conditions_met': False,
                    'signal_type': None,  # 'buy' or 'sell'
                    'start_time': None,
                    'start_price': None,
                    'current_deviation': 0,
                    'ma_invalidated': False,
                    'duration': 0,
                    'conditions': {
                        'trend_aligned': False,
                        'momentum_confirmed': False,
                        'volatility_suitable': False,
                        'ma_alignment': False
                    }
                } for tf in (timeframes or [])
            } for symbol in (symbols or [])
        }
        
        # Create an event to signal monitoring thread to stop
        self.stop_monitoring = threading.Event()
        
        # Create a thread for background monitoring
        self.monitoring_thread = None

    def _setup_logging(self):
        log_folder = "live_trading_logs"
        os.makedirs(log_folder, exist_ok=True)
        log_file = os.path.join(log_folder, f"trading_log_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log")
        
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)
        
        # Custom formatter using TerminalManager colors
        class ColoredFormatter(logging.Formatter):
            def format(self, record):
                if record.levelno >= logging.ERROR:
                    color = self.terminal.COLORS['red']
                elif record.levelno >= logging.WARNING:
                    color = self.terminal.COLORS['yellow']
                elif record.levelno >= logging.INFO:
                    color = self.terminal.COLORS['green']
                else:
                    color = self.terminal.COLORS['blue']
                
                record.msg = f"{color}{record.msg}{self.terminal.COLORS['reset']}"
                return super().format(record)
        
        # Set up handlers with the new formatter
        formatter = ColoredFormatter('%(asctime)s | %(levelname)s | %(message)s')
        
        # Console handler
        ch = logging.StreamHandler()
        ch.setFormatter(formatter)
        self.logger.addHandler(ch)
        
        # File handler
        fh = logging.FileHandler(log_file)
        fh.setFormatter(logging.Formatter('%(asctime)s | %(levelname)s | %(message)s'))
        self.logger.addHandler(fh)

    def update_status_line(self):
        """Update the status line with current system state."""
        try:
            # Get connection status
            mt5_status = "Connected" if self.mt5_connected else "Disconnected"
            telegram_status = "Connected" if self.telegram_connected else "Disconnected"
            
            # Get trade counts
            active_trades = sum(len(self.positions[s]) for s in self.symbols)
            mock_trades = len(self.mock_trade_manager.mock_trades)
            
            # Get profit
            daily_profit = sum(self.convert_to_points(self.daily_profit[s], s) for s in self.symbols)
            
            status = (
                f"Last Update: {datetime.now().strftime('%H:%M:%S')} | "
                f"MT5: {mt5_status} | Telegram: {telegram_status} | "
                f"Active Trades: {active_trades} | Mock Trades: {mock_trades} | "
                f"Daily Profit: {daily_profit:.1f} pts"
            )
            
            self.terminal.update_status(status)
        except Exception as e:
            self.logger.error(f"Error updating status line: {str(e)}")

    def parse_timeframe(self, tf_str):
        tf_str = tf_str.upper()
        return self.timeframe_configs.get(tf_str)

    def get_timeframe_name(self, timeframe):
        for name, value in self.timeframe_configs.items():
            if value == timeframe:
                return name
        return "Unknown"

    def get_telegram_updates(self):
        """Enhanced Telegram updates with proper offset handling and better timeout handling."""
        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/getUpdates"
        
        retry_count = 0
        while retry_count < self.max_retries:
            try:
                params = {
                    "offset": self.telegram_offset,
                    "timeout": 30,
                    "allowed_updates": ["message"]
                }
                
                # Increase timeout and add backoff strategy
                response = requests.get(url, params=params, timeout=60)
                response.raise_for_status()
                
                updates = response.json()
                if updates.get("ok") and "result" in updates:
                    if updates["result"]:
                        latest_update = max(update["update_id"] for update in updates["result"])
                        self.telegram_offset = latest_update + 1
                        self.save_telegram_offset()
                    return updates
                    
                time.sleep(1)
                
            except requests.exceptions.Timeout:
                retry_count += 1
                self.logger.warning(f"Telegram timeout (attempt {retry_count}/{self.max_retries}), retrying...")
                time.sleep(5 * retry_count)  # Progressive backoff
            except requests.exceptions.RequestException as e:
                retry_count += 1
                self.logger.error(f"Failed to get Telegram updates (attempt {retry_count}/{self.max_retries}): {str(e)}")
                if retry_count == self.max_retries:
                    time.sleep(60)
                    retry_count = 0
                else:
                    time.sleep(5 * retry_count)
        
        return None

    def save_telegram_offset(self):
        """Save Telegram offset to file."""
        try:
            with open("telegram_offset.txt", "w") as f:
                f.write(str(self.telegram_offset))
        except Exception as e:
            self.logger.error(f"Failed to save Telegram offset: {e}")

    def load_telegram_offset(self):
        """Load Telegram offset from file."""
        try:
            if os.path.exists("telegram_offset.txt"):
                with open("telegram_offset.txt", "r") as f:
                    self.telegram_offset = int(f.read().strip())
        except Exception as e:
            self.logger.error(f"Failed to load Telegram offset: {e}")

    def send_telegram_message(self, message, thread_id=None, chart_path=None, chat_id=None):
        """Enhanced Telegram message sending with better timeout handling"""
        if not self.TELEGRAM_BOT_TOKEN or not self.TELEGRAM_CHAT_ID:
            self.logger.warning("Telegram credentials not configured")
            return None

        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendMessage"
        max_length = 4096
        chat_id = chat_id or self.TELEGRAM_CHAT_ID
        
        # Format message
        formatted_message = f"> GC_Signals:\n{message}"
        formatted_message = formatted_message.replace('<', '&lt;').replace('>', '&gt;')
        
        # Split long messages
        if len(formatted_message) > max_length:
            parts = []
            current_part = "> GC_Signals:\n"
            for line in message.split('\n'):
                if len(current_part) + len(line) + 1 <= max_length:
                    current_part += line + '\n'
                else:
                    parts.append(current_part.strip())
                    current_part = f"> GC_Signals:\n{line}\n"
            if current_part:
                parts.append(current_part.strip())
        else:
            parts = [formatted_message]
        
        last_message_id = None
        for part in parts:
            retry_count = 0
            while retry_count < self.max_retries:
                try:
                    payload = {
                        "chat_id": chat_id,
                        "text": part,
                        "parse_mode": "HTML"
                    }
                    
                    if thread_id and not last_message_id:
                        payload["reply_to_message_id"] = thread_id
                    elif last_message_id:
                        payload["reply_to_message_id"] = last_message_id

                    response = requests.post(url, json=payload, timeout=30)  # Increased timeout
                    response.raise_for_status()
                    
                    result = response.json()
                    if not result.get("ok"):
                        raise Exception(f"Telegram API error: {result.get('description')}")
                        
                    last_message_id = result.get("result", {}).get("message_id")
                    
                    # Send chart if available
                    if chart_path and last_message_id and part == parts[-1]:
                        try:
                            with open(chart_path, 'rb') as chart_file:
                                files = {'photo': chart_file}
                                photo_url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendPhoto"
                                photo_response = requests.post(
                                    photo_url,
                                    data={"chat_id": chat_id, "reply_to_message_id": last_message_id},
                                    files=files,
                                    timeout=30  # Increased timeout
                                )
                                photo_response.raise_for_status()
                        except Exception as e:
                            self.logger.error(f"Failed to send chart: {e}")
                    
                    break
                    
                except Exception as e:
                    retry_count += 1
                    self.logger.error(f"Failed to send Telegram message (attempt {retry_count}/{self.max_retries}): {e}")
                    if retry_count == self.max_retries:
                        return None
                    time.sleep(5 * retry_count)  # Progressive backoff
        
        return last_message_id

    def load_trade_history(self):
        for symbol in self.symbols:
            for filename, history_dict in [
                (f"trade_history_{symbol}.json", self.trade_history),
                (f"grid_history_{symbol}.json", self.grid_history),
                (f"suretrend_history_{symbol}.json", self.suretrend_history),
                (f"momentum_history_{symbol}.json", self.momentum_history)
            ]:
                if os.path.exists(filename):
                    with open(filename, 'r') as f:
                        try:
                            history_dict[symbol] = json.load(f)
                            self.logger.info(f"[{symbol}] Loaded {len(history_dict[symbol])} trades from {filename}")
                        except json.JSONDecodeError:
                            self.logger.error(f"[{symbol}] Failed to load {filename}")

    def save_trade_history(self):
        for symbol in self.symbols:
            for filename, history_dict in [
                (f"trade_history_{symbol}.json", self.trade_history),
                (f"grid_history_{symbol}.json", self.grid_history),
                (f"suretrend_history_{symbol}.json", self.suretrend_history),
                (f"momentum_history_{symbol}.json", self.momentum_history)
            ]:
                with open(filename, 'w') as f:
                    json.dump(history_dict[symbol], f, default=str)

    def cleanup(self):
        self.logger.info("Cleaning up...")
        try:
            # Stop status thread
            self.status_thread_running = False
            if hasattr(self, 'status_thread'):
                self.status_thread.join(timeout=2)
            
            # Existing cleanup code...
            with self.command_lock:
                for symbol in self.symbols:
                    for position in list(self.positions[symbol].values()):
                        self.close_position(position, "System shutdown")
                self.save_trade_history()
                
            # Ensure proper MT5 shutdown
            if mt5.terminal_info():
                mt5.shutdown()
                
            # Additional cleanup for background terminal
            try:
                subprocess.run(['taskkill', '/F', '/IM', 'terminal64.exe'], capture_output=True)
            except Exception as e:
                self.logger.warning(f"Failed to force close MT5 terminal: {e}")
        except Exception as e:
            self.logger.error(f"Error during cleanup: {e}")

    def handle_exit(self, e):
        if e.name == 'q':
            self.cleanup()
            os._exit(0)

    def ensure_mt5_connection(self):
        """Enhanced MT5 connection handling with better retry logic"""
        if self.simulate:
            return True

        try:
            # First check if we're already connected
            if mt5.terminal_info() and mt5.account_info():
                return True

            # If not connected, try to initialize
            if not mt5.initialize():
                # Kill any existing MT5 processes first
                try:
                    import subprocess
                    import psutil
                    for proc in psutil.process_iter(['pid', 'name']):
                        try:
                            if proc.info['name'].lower() in ['terminal64.exe', 'metatrader.exe', 'metaeditor64.exe']:
                                subprocess.run(['taskkill', '/F', '/PID', str(proc.info['pid'])], capture_output=True)
                        except (psutil.NoSuchProcess, psutil.AccessDenied):
                            continue
                    time.sleep(2)  # Give time for processes to terminate
                except Exception as e:
                    self.logger.warning(f"Failed to kill existing MT5 processes: {e}")

                # Create a temporary directory for MT5 data
                temp_dir = tempfile.mkdtemp(prefix="mt5_temp_")
                self.logger.info(f"Created temporary directory for MT5: {temp_dir}")

                # Initialize with retries
                for attempt in range(3):
                    try:
                        initialized = mt5.initialize(
                            path=self.mt5_path,
                            login=self.mt5_login,
                            password=self.mt5_password,
                            server=self.mt5_server,
                            portable=True,
                            timeout=60000,
                            config={
                                "show": False,
                                "autoclose": True,
                                "silent": True
                            }
                        )

                        if initialized:
                            # Verify connection
                            if not mt5.account_info():
                                raise Exception("Failed to get account info after initialization")
                            
                            # Initialize symbols
                            for symbol in self.symbols:
                                if not mt5.symbol_select(symbol, True):
                                    raise Exception(f"Failed to select symbol {symbol}")
                                
                                symbol_info = mt5.symbol_info(symbol)
                                if not symbol_info:
                                    raise Exception(f"Failed to get symbol info for {symbol}")
                                
                                self.point[symbol] = symbol_info.point
                                self.symbol_info[symbol] = {
                                    'digits': symbol_info.digits,
                                    'trade_contract_size': symbol_info.trade_contract_size,
                                    'volume_min': symbol_info.volume_min,
                                    'volume_max': symbol_info.volume_max,
                                    'volume_step': symbol_info.volume_step
                                }
                            
                            self.mt5_connected = True
                            return True

                        error = mt5.last_error()
                        if attempt < 2:
                            self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed: {error}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {attempt + 1} attempts: {error}")
                            return False

                    except Exception as e:
                        if attempt < 2:
                            self.logger.warning(f"MT5 initialization error (attempt {attempt + 1}): {str(e)}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {attempt + 1} attempts with error: {str(e)}")
                            return False

            return False

        except Exception as e:
            self.logger.error(f"Error in ensure_mt5_connection: {str(e)}")
            return False

    def initialize_mt5(self):
        """Initialize MT5 connection and point values for all symbols."""
        # Initialize self.point as a dictionary if not already
        if not hasattr(self, 'point') or not isinstance(self.point, dict):
            self.point = {}
    
        if self.simulate:
            # Initialize point values for simulation mode
            for symbol in self.symbols:
                self.point[symbol] = 0.01 if symbol != "XAUUSD" else 0.01
            self.logger.info("Running in simulation mode; MT5 not initialized.")
            return True
    
        try:
            # First, ensure MT5 is completely shut down
            if mt5.terminal_info():
                mt5.shutdown()
            
            # Force kill any existing MT5 processes
            try:
                import subprocess
                import psutil
                
                # Kill terminal64.exe processes
                for proc in psutil.process_iter(['pid', 'name']):
                    try:
                        if proc.info['name'].lower() in ['terminal64.exe', 'metatrader.exe', 'metaeditor64.exe']:
                            subprocess.run(['taskkill', '/F', '/PID', str(proc.info['pid'])], capture_output=True)
                    except (psutil.NoSuchProcess, psutil.AccessDenied):
                        continue
                
                time.sleep(2)  # Give time for processes to terminate
            except Exception as e:
                self.logger.warning(f"Failed to kill existing MT5 processes: {e}")
    
            # Create a temporary directory for MT5 data
            import tempfile
            import shutil
            temp_dir = tempfile.mkdtemp(prefix="mt5_temp_")
            self.logger.info(f"Created temporary directory for MT5: {temp_dir}")
    
            # Initialize MT5 with retries
            max_retries = 3
            for attempt in range(max_retries):
                try:
                    # Initialize with minimal settings first
                    initialized = mt5.initialize(
                        path=self.mt5_path,
                        login=self.mt5_login,
                        password=self.mt5_password,
                        server=self.mt5_server,
                        portable=True,
                        timeout=60000,
                        config={
                            "show": False,
                            "autoclose": True,
                            "silent": True
                        }
                    )
    
                    if not initialized:
                        error = mt5.last_error()
                        if attempt < max_retries - 1:
                            self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed: {error}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {max_retries} attempts: {error}")
                            shutil.rmtree(temp_dir, ignore_errors=True)
                            return False
    
                    # Verify connection and login
                    account_info = mt5.account_info()
                    if not account_info:
                        self.logger.error("Failed to get account info")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
                    # Verify trading is enabled
                    terminal = mt5.terminal_info()
                    if not terminal:
                        self.logger.error("Failed to get terminal info")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
                    if not terminal.trade_allowed:
                        self.logger.warning("AutoTrading is disabled, attempting to enable...")
                        # We'll continue anyway as it might be enabled later
    
                    self.logger.info(f"Successfully connected to account {account_info.login} on {self.mt5_server}")
                    self.logger.info(f"Balance: ${account_info.balance:.2f}, Equity: ${account_info.equity:.2f}")
                    self.logger.info(f"Margin Level: {account_info.margin_level:.2f}%")
                    
                    # Initialize symbols
                    for symbol in self.symbols:
                        if not mt5.symbol_select(symbol, True):
                            self.logger.error(f"Failed to select symbol {symbol}")
                            continue
                        
                        symbol_info = mt5.symbol_info(symbol)
                        if symbol_info:
                            # Store point value in dictionary
                            self.point[symbol] = symbol_info.point
                            self.symbol_info[symbol] = {
                                'digits': symbol_info.digits,
                                'trade_contract_size': symbol_info.trade_contract_size,
                                'volume_min': symbol_info.volume_min,
                                'volume_max': symbol_info.volume_max,
                                'volume_step': symbol_info.volume_step
                            }
                            self.logger.info(f"Initialized {symbol}: Point={symbol_info.point}, "
                                           f"Digits={symbol_info.digits}, "
                                           f"Contract Size={symbol_info.trade_contract_size}")
                        else:
                            self.logger.error(f"Failed to get symbol info for {symbol}")
                            self.point[symbol] = 0.01  # Fallback point value
                            continue  # Try to continue with other symbols
    
                    # Validate that all symbols have point values
                    for symbol in self.symbols:
                        if symbol not in self.point:
                            self.logger.warning(f"No point value set for {symbol}, using fallback value 0.01")
                            self.point[symbol] = 0.01
    
                    self.mt5_connected = True
                    return True
    
                except Exception as e:
                    if attempt < max_retries - 1:
                        self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed with error: {str(e)}. Retrying...")
                        time.sleep(5)
                    else:
                        self.logger.error(f"MT5 initialization failed after {max_retries} attempts with error: {str(e)}")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
        except Exception as e:
            self.logger.error(f"Error in initialize_mt5: {str(e)}")
            return False
        finally:
            # Clean up temporary directory if it exists
            try:
                if 'temp_dir' in locals():
                    shutil.rmtree(temp_dir, ignore_errors=True)
            except Exception as e:
                self.logger.warning(f"Failed to clean up temporary directory: {e}")

    def add_account(self, name, login, password, server):
        if name in self.accounts:
            self.logger.warning(f"Account '{name}' already exists.")
            return False
        self.accounts[name] = {"login": int(login), "password": password, "server": server}
        self.logger.info(f"Added account '{name}' with login {login} and server {server}.")
        # If no current account is set, make this the default and initialize
        if not self.current_account:
            self.current_account = name
            self.mt5_login = login
            self.mt5_password = password
            self.mt5_server = server
            if not self.initialize_mt5():
                self.logger.error(f"Failed to initialize MT5 with new account '{name}'.")
                del self.accounts[name]
                return False
        return True

    def load_daily_balance(self):
        """Load daily balance tracking information from file."""
        try:
            if os.path.exists(self.balance_file):
                with open(self.balance_file, 'r') as f:
                    data = json.load(f)
                    # Check if data is from today
                    saved_date = datetime.strptime(data.get('date', ''), '%Y-%m-%d').date()
                    if saved_date == datetime.now().date():
                        self.initial_balance = data.get('initial_balance')
                        self.lowest_balance = data.get('lowest_balance')
                        self.trading_locked = data.get('trading_locked', False)
                        self.trading_lock_reason = data.get('lock_reason', '')
                    else:
                        # New day, get fresh balance
                        self.initialize_daily_balance()
            else:
                self.initialize_daily_balance()
        except Exception as e:
            self.logger.error(f"Error loading daily balance: {str(e)}")
            self.initialize_daily_balance()


    def initialize_daily_balance(self):
        """Initialize daily balance tracking with current MT5 account balance."""
        try:
            if not self.simulate:
                # First ensure MT5 connection
                if not self.ensure_mt5_connection():
                    self.logger.error("Failed to connect to MT5 for balance initialization")
                    return
    
                # Get actual account balance from MT5
                account_info = mt5.account_info()
                if account_info:
                    self.initial_balance = account_info.balance
                    self.lowest_balance = account_info.balance
                    self.trading_locked = False
                    self.trading_lock_reason = ""
                    self.logger.info(f"Initialized daily balance tracking with MT5 balance: ${self.initial_balance:.2f}")
                else:
                    # Log error and exit if can't get balance
                    self.logger.error("Failed to get MT5 account balance")
                    return
            else:
                # For simulation, get actual balance first
                account_info = mt5.account_info()
                if account_info:
                    self.initial_balance = account_info.balance
                else:
                    self.initial_balance = 146.52  # Use current actual balance as fallback
                self.lowest_balance = self.initial_balance
                self.trading_locked = False
                self.trading_lock_reason = ""
    
            self.save_daily_balance()
    
        except Exception as e:
            self.logger.error(f"Error initializing daily balance: {str(e)}")
            # Do not set any default values, just log error and return
            return

    def save_daily_balance(self):
        """Save daily balance tracking information to file."""
        try:
            data = {
                'date': datetime.now().strftime('%Y-%m-%d'),
                'initial_balance': self.initial_balance,
                'lowest_balance': self.lowest_balance,
                'trading_locked': self.trading_locked,
                'lock_reason': self.trading_lock_reason
            }
            with open(self.balance_file, 'w') as f:
                json.dump(data, f)
        except Exception as e:
            self.logger.error(f"Error saving daily balance: {str(e)}")

    def check_drawdown(self):
        """Check if current drawdown exceeds maximum allowed percentage."""
        try:
            if not self.initial_balance:
                return False

            current_balance = 0
            if not self.simulate:
                # Get fresh balance from MT5
                account_info = mt5.account_info()
                if account_info:
                    current_balance = account_info.balance
                else:
                    self.logger.error("Failed to get current MT5 balance")
                    return False
            else:
                # In simulation mode, calculate from tracked profits
                current_balance = self.initial_balance + sum(self.daily_profit.values())

            # Skip drawdown check if initial balance is zero or null
            if not self.initial_balance:
                return False

            # Update lowest balance if current is lower
            if self.lowest_balance is None or current_balance < self.lowest_balance:
                self.lowest_balance = current_balance
                self.save_daily_balance()

            # Calculate drawdown percentage using actual values
            drawdown_percent = ((self.initial_balance - current_balance) / self.initial_balance) * 100 if self.initial_balance > 0 else 0

            if drawdown_percent >= self.max_drawdown_percent:
                message = (
                    f"⚠️ MAXIMUM DRAWDOWN REACHED ⚠️\n"
                    f"Initial Balance: ${self.initial_balance:.2f}\n"
                    f"Current Balance: ${current_balance:.2f}\n"
                    f"Drawdown: {drawdown_percent:.2f}%\n"
                    f"Trading will be locked for the rest of the day."
                )
                self.lock_trading(message)
                self.save_daily_balance()
                return True

            return False

        except Exception as e:
            self.logger.error(f"Error checking drawdown: {str(e)}")
            return False

    def switch_account(self, name):
        if name not in self.accounts:
            self.logger.error(f"Account '{name}' not found.")
            return False
        if name == self.current_account:
            self.logger.info(f"Already on account '{name}'.")
            return True
        
        # Store current positions before switching
        current_positions = {symbol: dict(self.positions[symbol]) for symbol in self.symbols}
        
        # Update current account details
        self.current_account = name
        self.mt5_login = self.accounts[name]["login"]
        self.mt5_password = self.accounts[name]["password"]
        self.mt5_server = self.accounts[name]["server"]
        
        # Reinitialize MT5 with new account
        if not self.initialize_mt5():
            self.logger.error(f"Failed to switch to account '{name}'.")
            return False
        
        # Restore positions or sync with new account
        self.positions = {symbol: {} for symbol in self.symbols}  # Reset positions
        self.sync_positions_with_mt5()
        
        self.logger.info(f"Switched to account '{name}' successfully.")
        return True

    def sync_positions_with_mt5(self):
        """Enhanced synchronization with MT5 including proper script trade tracking."""
        if self.simulate:
            return True

        try:
            # Get all current MT5 positions
            mt5_positions = mt5.positions_get()
            if mt5_positions is None:
                self.logger.error("Failed to get positions from MT5")
                return False
                
            mt5_tickets = {pos.ticket for pos in mt5_positions}
            
            # Use a timeout context for the lock
            if not self.command_lock.acquire(timeout=5):
                self.logger.error("Failed to acquire lock for position synchronization")
                return False
                
            try:
                for symbol in self.symbols:
                    # Check for positions that exist in our tracking but not in MT5
                    for ticket in list(self.positions[symbol].keys()):
                        if ticket not in mt5_tickets:
                            # Position was closed externally
                            position = self.positions[symbol][ticket]
                            self.logger.info(f"[{symbol}] Position {ticket} closed externally, updating records")
                            
                            # Calculate final profit if possible
                            profit_points = 0
                            if mt5_positions:
                                for mt5_pos in mt5_positions:
                                    if mt5_pos.ticket == ticket:
                                        profit_points = self.convert_to_points(mt5_pos.profit, symbol)
                                        break
                            
                            # Update trade history
                            self.update_trade_history_on_close(ticket, symbol, profit_points, "Closed externally")
                            
                            # Remove from tracking
                            del self.positions[symbol][ticket]
                    
                    # Add any new positions from MT5 that we're not tracking
                    for pos in mt5_positions:
                        if pos.symbol == symbol and pos.ticket not in self.positions[symbol]:
                            # Check if this is a script-placed trade based on comment
                            is_script_trade = pos.comment and pos.comment.startswith("GC_Signals_")
                            strategy = pos.comment.replace("GC_Signals_", "") if is_script_trade else "external"
                            
                            if not is_script_trade:
                                # This is an external trade - add it with external trade handling
                                self.handle_external_trade(pos)
                            else:
                                # This is our trade that somehow got disconnected - restore it
                                self.positions[symbol][pos.ticket] = {
                                    'ticket': pos.ticket,
                                    'type': pos.type,
                                    'entry_price': pos.price_open,
                                    'lot_size': pos.volume,
                                    'sl': pos.sl,
                                    'tp': pos.tp,
                                    'timeframe': mt5.TIMEFRAME_M1,  # Default to M1 if unknown
                                    'strategy': strategy,
                                    'entry_time': datetime.fromtimestamp(pos.time).strftime('%Y-%m-%d %H:%M:%S.%f'),
                                    'signal_time': datetime.fromtimestamp(pos.time).strftime('%Y-%m-%d %H:%M:%S.%f'),
                                    'breakeven_triggered': False,
                                    'trailing_active': False,
                                    'thread_id': None,
                                    'reason': strategy,
                                    'comments': pos.comment,
                                    'symbol': symbol,
                                    'profit': pos.profit,
                                    'script_placed': True
                                }
                                self.logger.info(f"[{symbol}] Restored script-placed trade {pos.ticket}")
            finally:
                self.command_lock.release()
            
            self.save_trade_history()
            return True
            
        except Exception as e:
            self.logger.error(f"Error in sync_positions_with_mt5: {str(e)}")
            if self.command_lock.locked():
                self.command_lock.release()
            return False

    def prompt_position_params(self, position):
        """Prompt for position parameters after trade entry."""
        symbol = position['symbol']
        point = self.point[symbol]  # Get point value directly from self.point dictionary
        
        # Calculate current parameters in points
        current_sl_points = abs(position['sl'] - position['entry_price']) / point if position['sl'] else 0
        current_tp_points = abs(position['tp'] - position['entry_price']) / point if position['tp'] else 0
        
        message = (
            f"🔧 Position Parameters Required:\n"
            f"Ticket: {position['ticket']}\n"
            f"Symbol: {symbol}\n"
            f"Entry: {position['entry_price']:.5f}\n"
            f"Current Settings:\n"
            f"- SL: {current_sl_points:.0f} points\n"
            f"- TP: {current_tp_points:.0f} points\n"
            f"- Trail Stop: {self.trailing_stop_configs[position['timeframe']]:.1f} points\n"
            f"- Trail Delay: {self.trailing_delay_configs[position['timeframe']]:.1f} points\n"
            f"- MA Exit: {'Enabled' if self.ma_exit_enabled[symbol][position['timeframe']] else 'Disabled'}\n\n"
            f"Reply with: setparams <ticket> <sl_points> <tp_points> <trail_stop> <trail_delay> <ma_exit>\n"
            f"Example: setparams {position['ticket']} 100 200 20 50 1\n"
            f"(Use 0 for default values, 1/0 for ma_exit enable/disable)"
        )
        
        # Send to both interfaces
        self.send_telegram_message(message)
        print(f"\n{message}")
        position['waiting_params'] = True

    def handle_position_params(self, cmd_parts):
        """Handle the setparams command for position parameters."""
        try:
            if len(cmd_parts) != 7:
                return "Invalid parameters. Usage: setparams <ticket> <sl_points> <tp_points> <trail_stop> <trail_delay> <ma_exit>"
            
            _, ticket, sl_points, tp_points, trail_stop, trail_delay, ma_exit = cmd_parts
            ticket = int(ticket)
            
            # Find position
            position = None
            symbol = None
            for sym in self.symbols:
                if ticket in self.positions[sym]:
                    position = self.positions[sym][ticket]
                    symbol = sym
                    break
            
            if not position:
                return f"Position with ticket {ticket} not found."
            
            if not position.get('waiting_params', False):
                return f"Position {ticket} is not waiting for parameter settings."
            
            # Get symbol point value
            point = self.point[symbol]
            
            # Calculate actual SL/TP prices based on points
            sl_points = float(sl_points)
            tp_points = float(tp_points)
            
            if sl_points > 0:
                sl = (position['entry_price'] - sl_points * point) if position['type'] == mt5.ORDER_TYPE_BUY else \
                    (position['entry_price'] + sl_points * point)
            else:
                sl = position['sl']
                
            if tp_points > 0:
                tp = (position['entry_price'] + tp_points * point) if position['type'] == mt5.ORDER_TYPE_BUY else \
                    (position['entry_price'] - tp_points * point)
            else:
                tp = position['tp']
            
            trail_stop = float(trail_stop) if float(trail_stop) != 0 else self.trailing_stop_configs[position['timeframe']]
            trail_delay = float(trail_delay) if float(trail_delay) != 0 else self.trailing_delay_configs[position['timeframe']]
            ma_exit = bool(int(ma_exit))
            
            # Apply parameters
            success = self.modify_position(position, sl=sl, tp=tp)
            if not success:
                return "Failed to modify position parameters"
                
            self.trailing_stop_configs[position['timeframe']] = trail_stop
            self.trailing_delay_configs[position['timeframe']] = trail_delay
            self.ma_exit_enabled[symbol][position['timeframe']] = ma_exit
            
            position['waiting_params'] = False
            
            return (f"Parameters set for ticket {ticket}:\n"
                    f"SL: {sl_points:.0f} points (Price: {sl:.5f})\n"
                    f"TP: {tp_points:.0f} points (Price: {tp:.5f})\n"
                    f"Trail Stop: {trail_stop} points\n"
                    f"Trail Delay: {trail_delay} points\n"
                    f"MA Exit: {'Enabled' if ma_exit else 'Disabled'}")
                    
        except Exception as e:
            return f"Error setting parameters: {str(e)}"

    def generate_trade_report(self, ticket=None, symbol=None, daily=False):
        """Generate detailed trade report in PDF format with embedded charts including Parabolic SAR and MACD using TA-Lib."""
        try:
            # Create PDF document
            filename = f"trade_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.pdf"
            filepath = os.path.join(self.reports_folder, filename)
            
            doc = SimpleDocTemplate(filepath, pagesize=letter)
            story = []
            
            # Get trades to report
            trades = []
            title = ""
            if ticket:
                # For ticket-specific report
                title = f"TRADE REPORT TICKET No. {ticket}"
                for sym in self.symbols:
                    # Check current open positions
                    if ticket in self.positions[sym]:
                        position = self.positions[sym][ticket]
                        trade = {
                            'ticket': position['ticket'],
                            'type': "BUY" if position['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                            'entry_price': position['entry_price'],
                            'close_price': None,
                            'sl': position['sl'],
                            'tp': position['tp'],
                            'lot_size': position['lot_size'],
                            'entry_time': position['entry_time'],
                            'close_time': None,
                            'symbol': sym,
                            'timeframe': position['timeframe'],
                            'profit': position['profit'],
                            'reason': position.get('reason', 'Manual/External Trade'),
                            'comments': position.get('comments', ''),
                            'status': 'open'
                        }
                        trades.append(trade)
                    
                    # Check all history categories
                    for history_list in [
                        self.trade_history[sym],
                        self.grid_history[sym],
                        self.suretrend_history[sym],
                        self.momentum_history[sym]
                    ]:
                        trades.extend([t for t in history_list if t.get('ticket') == ticket])
                    
                    # Get MT5 history for the ticket
                    if not self.simulate:
                        mt5_history = mt5.history_deals_get(ticket=ticket)
                        if mt5_history:
                            for deal in mt5_history:
                                if not any(t.get('ticket') == deal.ticket for t in trades):
                                    trades.append({
                                        'ticket': deal.ticket,
                                        'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                        'entry_price': deal.price,
                                        'close_price': deal.price,
                                        'sl': 0.0,
                                        'tp': 0.0,
                                        'lot_size': deal.volume,
                                        'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'symbol': deal.symbol,
                                        'timeframe': 'M1',
                                        'profit': deal.profit,
                                        'reason': 'External MT5 Trade',
                                        'comments': deal.comment,
                                        'status': 'closed'
                                    })
                    
            elif symbol:
                # For symbol-specific report
                title = f"TRADE REPORT {symbol}"
                # Include current open positions
                for pos in self.positions[symbol].values():
                    trades.append({
                        'ticket': pos['ticket'],
                        'type': "BUY" if pos['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                        'entry_price': pos['entry_price'],
                        'close_price': None,
                        'sl': pos['sl'],
                        'tp': pos['tp'],
                        'lot_size': pos['lot_size'],
                        'entry_time': pos['entry_time'],
                        'close_time': None,
                        'symbol': symbol,
                        'timeframe': pos['timeframe'],
                        'profit': pos['profit'],
                        'reason': pos.get('reason', 'Manual/External Trade'),
                        'comments': pos.get('comments', ''),
                        'status': 'open'
                    })
                
                # Add all historical trades
                trades.extend(self.trade_history[symbol])
                trades.extend(self.grid_history[symbol])
                trades.extend(self.suretrend_history[symbol])
                trades.extend(self.momentum_history[symbol])
                
                # Get MT5 history for the symbol
                if not self.simulate:
                    mt5_history = mt5.history_deals_get(
                        datetime.now() - timedelta(days=7),
                        datetime.now(),
                        symbol=symbol
                    )
                    if mt5_history:
                        for deal in mt5_history:
                            if not any(t.get('ticket') == deal.ticket for t in trades):
                                trades.append({
                                    'ticket': deal.ticket,
                                    'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                    'entry_price': deal.price,
                                    'close_price': deal.price,
                                    'sl': 0.0,
                                    'tp': 0.0,
                                    'lot_size': deal.volume,
                                    'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                    'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                    'symbol': symbol,
                                    'timeframe': 'M1',
                                    'profit': deal.profit,
                                    'reason': 'External MT5 Trade',
                                    'comments': deal.comment,
                                    'status': 'closed'
                                })
                    
            elif daily:
                # For daily report
                title = f"DAILY TRADE REPORT {datetime.now().strftime('%Y-%m-%d')}"
                today = datetime.now().date()
                
                for sym in self.symbols:
                    # Include current open positions opened today
                    for pos in self.positions[sym].values():
                        if self.parse_trade_time(pos['entry_time']).date() == today:
                            trades.append({
                                'ticket': pos['ticket'],
                                'type': "BUY" if pos['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                                'entry_price': pos['entry_price'],
                                'close_price': None,
                                'sl': pos['sl'],
                                'tp': pos['tp'],
                                'lot_size': pos['lot_size'],
                                'entry_time': pos['entry_time'],
                                'close_time': None,
                                'symbol': sym,
                                'timeframe': pos['timeframe'],
                                'profit': pos['profit'],
                                'reason': pos.get('reason', 'Manual/External Trade'),
                                'comments': pos.get('comments', ''),
                                'status': 'open'
                            })
                    
                    # Add all historical trades from today
                    for history_list in [
                        self.trade_history[sym],
                        self.grid_history[sym],
                        self.suretrend_history[sym],
                        self.momentum_history[sym]
                    ]:
                        trades.extend([t for t in history_list 
                                     if self.parse_trade_time(t.get('entry_time', '')).date() == today])
                    
                    # Get today's MT5 history
                    if not self.simulate:
                        today_start = datetime.combine(today, datetime.min.time())
                        mt5_history = mt5.history_deals_get(today_start, datetime.now(), symbol=sym)
                        if mt5_history:
                            for deal in mt5_history:
                                if not any(t.get('ticket') == deal.ticket for t in trades):
                                    trades.append({
                                        'ticket': deal.ticket,
                                        'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                        'entry_price': deal.price,
                                        'close_price': deal.price,
                                        'sl': 0.0,
                                        'tp': 0.0,
                                        'lot_size': deal.volume,
                                        'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'symbol': sym,
                                        'timeframe': 'M1',
                                        'profit': deal.profit,
                                        'reason': 'External MT5 Trade',
                                        'comments': deal.comment,
                                        'status': 'closed'
                                    })
            
            if not trades:
                return "No trades found for the specified criteria."
        
            # Add title
            story.append(Paragraph(title, ParagraphStyle('Title', fontSize=14, spaceAfter=20)))
            
            # Process trades
            for trade in trades:
                try:
                    # Get timeframe (handle both string and numeric formats)
                    trade_tf = trade.get('timeframe')
                    if isinstance(trade_tf, str):
                        timeframe = self.parse_timeframe(trade_tf)
                        tf_name = trade_tf
                    else:
                        timeframe = trade_tf
                        tf_name = self.get_timeframe_name(trade_tf)
                    
                    if not timeframe:
                        # If timeframe is invalid or missing, try to determine from trade history
                        time_diff = None
                        if trade.get('entry_time') and trade.get('close_time'):
                            entry = self.parse_trade_time(trade['entry_time'])
                            close = self.parse_trade_time(trade['close_time'])
                            time_diff = (close - entry).total_seconds()
                        
                        # Assign appropriate timeframe based on trade duration
                        if time_diff:
                            if time_diff <= 3600:  # 1 hour or less
                                timeframe = mt5.TIMEFRAME_M5
                                tf_name = 'M5'
                            elif time_diff <= 14400:  # 4 hours or less
                                timeframe = mt5.TIMEFRAME_M15
                                tf_name = 'M15'
                            else:
                                timeframe = mt5.TIMEFRAME_H1
                                tf_name = 'H1'
                        else:
                            # Default to M5 if can't determine
                            timeframe = mt5.TIMEFRAME_M5
                            tf_name = 'M5'
                    
                    # Trade placed details
                    trade_type = "Buy" if trade.get('type') == "BUY" else "Sell"
                    entry_details = (
                        f"Trade Placed: {trade_type} {trade.get('symbol', '')} {tf_name} "
                        f"Ticket no{trade.get('ticket', '')} placed {trade.get('entry_price', 0.0):.5f} "
                        f"due to {trade.get('reason', 'N/A')}"
                    )
                    story.append(Paragraph(entry_details, ParagraphStyle('Normal', spaceBefore=10)))
                    
                    # Add chart for the trade
                    symbol = trade.get('symbol')
                    entry_time = self.parse_trade_time(trade.get('entry_time', ''))
                    
                    # Get historical data around the trade time with appropriate timeframe
                    df = self.get_rates(symbol, timeframe=timeframe)
                    if df is not None:
                        df = self.calculate_indicators(df, timeframe, symbol)
                        
                        # Calculate Parabolic SAR and MACD using TA-Lib
                        import talib
                        import numpy as np
                        
                        # Ensure sufficient data for indicators
                        if len(df) < 26:  # Minimum for MACD slow EMA
                            self.logger.warning(f"Insufficient data for indicators on {symbol} {tf_name}: {len(df)} rows")
                            story.append(Paragraph(f"Insufficient data for indicators for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Convert to NumPy arrays for TA-Lib
                        high = np.array(df['high'], dtype=float)
                        low = np.array(df['low'], dtype=float)
                        close = np.array(df['close'], dtype=float)
                        
                        # Parabolic SAR
                        df['sar'] = talib.SAR(high, low, acceleration=0.02, maximum=0.2)
                        
                        # MACD
                        macd, macd_signal, macd_hist = talib.MACD(
                            close,
                            fastperiod=12,
                            slowperiod=26,
                            signalperiod=9
                        )
                        df['macd'] = macd
                        df['macd_signal'] = macd_signal
                        df['macd_hist'] = macd_hist
                        
                        # Create figure with subplots (main chart + MACD)
                        from plotly.subplots import make_subplots
                        fig = make_subplots(
                            rows=2, cols=1,
                            row_heights=[0.7, 0.3],
                            shared_xaxes=True,
                            vertical_spacing=0.1,
                            subplot_titles=[f"{symbol} {tf_name} Trade Chart", "MACD"]
                        )
                        
                        # Add candlestick chart to main plot (row 1)
                        fig.add_trace(
                            go.Candlestick(
                                x=df['time'],
                                open=df['open'],
                                high=df['high'],
                                low=df['low'],
                                close=df['close'],
                                name='OHLC'
                            ),
                            row=1, col=1
                        )
                        
                        # Add moving averages to main plot
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['ma_fast'],
                                mode='lines',
                                name=f'MA {self.ma_configs[timeframe]["fast"]}',
                                line=dict(color='blue')
                            ),
                            row=1, col=1
                        )
                        
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['ma_slow'],
                                mode='lines',
                                name=f'MA {self.ma_configs[timeframe]["slow"]}',
                                line=dict(color='red')
                            ),
                            row=1, col=1
                        )
                        
                        # Add Parabolic SAR to main plot
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['sar'],
                                mode='markers',
                                name='Parabolic SAR',
                                marker=dict(symbol='circle', size=5, color='purple')
                            ),
                            row=1, col=1
                        )
                        
                        # Add entry and exit points to main plot
                        entry_price = trade.get('entry_price')
                        exit_price = trade.get('close_price')
                        
                        fig.add_hline(y=entry_price, line_dash="dash", line_color="blue", annotation_text="Entry", row=1)
                        if exit_price:
                            fig.add_hline(y=exit_price, line_dash="dash", line_color="red", annotation_text="Exit", row=1)
                        
                        # Add SL/TP lines if available to main plot
                        if trade.get('sl'):
                            fig.add_hline(y=trade['sl'], line_dash="dot", line_color="red", annotation_text="SL", row=1)
                        if trade.get('tp'):
                            fig.add_hline(y=trade['tp'], line_dash="dot", line_color="green", annotation_text="TP", row=1)
                        
                        # Add MACD to subplot (row 2)
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['macd'],
                                mode='lines',
                                name='MACD',
                                line=dict(color='blue')
                            ),
                            row=2, col=1
                        )
                        
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['macd_signal'],
                                mode='lines',
                                name='Signal',
                                line=dict(color='orange')
                            ),
                            row=2, col=1
                        )
                        
                        fig.add_trace(
                            go.Bar(
                                x=df['time'],
                                y=df['macd_hist'],
                                name='Histogram',
                                marker_color=df['macd_hist'].apply(lambda x: 'green' if x >= 0 else 'red')
                            ),
                            row=2, col=1
                        )
                        
                        # Add profit annotation to main plot
                        if trade.get('profit_points'):
                            fig.add_annotation(
                                x=df['time'].iloc[-1],
                                y=exit_price or df['close'].iloc[-1],
                                text=f"Profit: {trade.get('profit_points', 0):.2f} points",
                                showarrow=True,
                                arrowhead=1,
                                row=1, col=1
                            )
                        
                        # Update layout
                        fig.update_layout(
                            height=500,
                            margin=dict(l=50, r=50, t=50, b=50),
                            showlegend=True,
                            xaxis2=dict(title='Time'),
                            yaxis=dict(title='Price'),
                            yaxis2=dict(title='MACD')
                        )
                        
                        # Save chart as temporary image with absolute path
                        temp_chart = os.path.join(self.reports_folder, f"temp_chart_{trade.get('ticket')}.png")
                        try:
                            self.logger.debug(f"Attempting to write chart to {temp_chart}")
                            fig.write_image(temp_chart, engine="kaleido")
                            self.logger.debug(f"Chart written to {temp_chart}")
                        except Exception as e:
                            self.logger.error(f"Failed to write chart image {temp_chart}: {str(e)}")
                            story.append(Paragraph(f"Chart generation failed for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Verify file exists before adding to PDF
                        if not os.path.exists(temp_chart):
                            self.logger.error(f"Chart image {temp_chart} was not created.")
                            story.append(Paragraph(f"Chart missing for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Add chart to PDF
                        try:
                            img = Image(temp_chart)
                            img.drawHeight = 350
                            img.drawWidth = 500
                            story.append(img)
                            story.append(Spacer(1, 20))
                        except Exception as e:
                            self.logger.error(f"Failed to add chart {temp_chart} to PDF: {str(e)}")
                            story.append(Paragraph(f"Chart inclusion failed for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Clean up temporary file
                        try:
                            os.remove(temp_chart)
                            self.logger.debug(f"Deleted temporary chart {temp_chart}")
                        except Exception as e:
                            self.logger.warning(f"Failed to delete temporary chart {temp_chart}: {str(e)}")
                    
                    # Add SL/TP details
                    sl_tp_details = (
                        f"Initial SL: {trade.get('sl', 'N/A'):.5f}, "
                        f"TP: {trade.get('tp', 'N/A'):.5f}"
                    )
                    story.append(Paragraph(sl_tp_details, ParagraphStyle('Normal', leftIndent=20)))
                    
                    # Add close details if trade is closed
                    if trade.get('close_time'):
                        close_details = (
                            f"Trade Closed: The trade {trade_type} {trade.get('symbol', '')} {tf_name} "
                            f"Ticket no{trade.get('ticket', '')} was closed at {trade.get('close_time', '')} "
                            f"due to {trade.get('close_reason', 'N/A')}"
                        )
                        story.append(Paragraph(close_details, ParagraphStyle('Normal', spaceBefore=10)))
                    
                    story.append(Spacer(1, 20))
                    
                except Exception as e:
                    self.logger.error(f"Error processing trade {trade.get('ticket', 'unknown')}: {str(e)}")
                    continue
            
            # Build PDF
            doc.build(story)
            
            # Send report via Telegram if available
            if self.TELEGRAM_BOT_TOKEN and self.TELEGRAM_CHAT_ID:
                try:
                    with open(filepath, 'rb') as f:
                        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendDocument"
                        files = {'document': f}
                        data = {'chat_id': self.TELEGRAM_CHAT_ID}
                        response = requests.post(url, data=data, files=files)
                        if not response.json().get('ok'):
                            self.logger.error(f"Failed to send report via Telegram: {response.json()}")
                except Exception as e:
                    self.logger.error(f"Error sending report via Telegram: {str(e)}")
            
            return f"Report generated successfully: {filepath}"
            
        except Exception as e:
            self.logger.error(f"Error generating trade report: {str(e)}")
            return f"Failed to generate report: {str(e)}"

    def monitor_suretrend_conditions(self):
        """Background thread to monitor SureTrend conditions for all symbols and timeframes."""
        while not self.stop_monitoring.is_set():
            try:
                for symbol in self.symbols:
                    for timeframe in self.timeframes:
                        # Get latest data
                        df = self.get_or_update_rates(symbol, timeframe)
                        if df is None or len(df) < 50:
                            continue
                            
                        # Calculate indicators
                        df = self.calculate_indicators(df, timeframe, symbol)
                        
                        # Check MA crossover for invalidation
                        ma_cross = self.check_ma_crossover(df)
                        current_price = df['close'].iloc[-1]
                        
                        # Get tracking data for this symbol/timeframe
                        tracking = self.suretrend_tracking[symbol][timeframe]
                        
                        # Check SureTrend conditions
                        signal_type, _, conditions = self.check_suretrend_signal(df, timeframe, symbol)
                        
                        # Update conditions tracking
                        if conditions:
                            tracking['conditions'].update(conditions)
                        
                        # Check if conditions are met
                        all_conditions_met = all(tracking['conditions'].values())
                        
                        # Handle condition state changes
                        if all_conditions_met and not tracking['conditions_met']:
                            # New signal detected
                            tracking['conditions_met'] = True
                            tracking['signal_type'] = signal_type
                            tracking['start_time'] = df.index[-1]
                            tracking['start_price'] = current_price
                            tracking['ma_invalidated'] = False
                        
                        # Update existing signal
                        if tracking['conditions_met']:
                            # Check for MA crossover invalidation
                            if (tracking['signal_type'] == 'buy' and ma_cross == 'sell') or \
                               (tracking['signal_type'] == 'sell' and ma_cross == 'buy'):
                                tracking['ma_invalidated'] = True
                                tracking['conditions_met'] = False
                            else:
                                # Update duration and deviation
                                if tracking['start_time']:
                                    tracking['duration'] = (df.index[-1] - tracking['start_time']).total_seconds()
                                    if tracking['start_price']:
                                        deviation = current_price - tracking['start_price']
                                        if tracking['signal_type'] == 'sell':
                                            deviation = -deviation
                                        tracking['current_deviation'] = deviation
                
                # Sleep for a short interval
                time.sleep(1)
                
            except Exception as e:
                self.logger.error(f"Error in SureTrend monitoring: {str(e)}")
                time.sleep(5)

    def start_suretrend_monitoring(self):
        """Start the background monitoring thread."""
        if self.monitoring_thread is None or not self.monitoring_thread.is_alive():
            self.stop_monitoring.clear()
            self.monitoring_thread = threading.Thread(target=self.monitor_suretrend_conditions)
            self.monitoring_thread.daemon = True
            self.monitoring_thread.start()
            return "SureTrend monitoring started"

    def stop_suretrend_monitoring(self):
        """Stop the background monitoring thread."""
        if self.monitoring_thread and self.monitoring_thread.is_alive():
            self.stop_monitoring.set()
            self.monitoring_thread.join()
            return "SureTrend monitoring stopped"

    def display_suretrend_checklist(self, symbol=None, timeframe=None):
        """Display the SureTrend conditions checklist."""
        symbols_to_check = [symbol] if symbol else self.symbols
        timeframes_to_check = [timeframe] if timeframe else self.timeframes
        
        output = []
        
        for sym in symbols_to_check:
            for tf in timeframes_to_check:
                tracking = self.suretrend_tracking[sym][tf]
                tf_name = self.get_timeframe_name(tf)
                
                output.append(f"\n=== SureTrend Checklist for {sym} {tf_name} ===")
                
                for cond_name, is_met in tracking['conditions'].items():
                    check = "✓" if is_met else "✗"
                    output.append(f"{check} {cond_name.replace('_', ' ').title()}")
                
                if tracking['conditions_met']:
                    signal_type = tracking['signal_type'].upper() if tracking['signal_type'] else 'UNKNOWN'
                    duration = timedelta(seconds=int(tracking['duration'])) if tracking['duration'] else timedelta()
                    deviation = tracking['current_deviation']
                    
                    output.append(f"\nSignal Type: {signal_type}")
                    output.append(f"Start Time: {tracking['start_time']}")
                    output.append(f"Duration: {duration}")
                    output.append(f"Price Deviation: {deviation:.5f}")
                    
                    if tracking['ma_invalidated']:
                        output.append("⚠️ WARNING: Signal invalidated by MA crossover!")
                
                output.append("")
        
        return "\n".join(output)

    def save_lock_state(self):
        """Save trading lock state to file."""
        try:
            lock_data = {
                'locked': self.trading_locked,
                'reason': self.trading_lock_reason,
                'date': datetime.now().strftime('%Y-%m-%d')
            }
            with open(self.lock_file, 'w') as f:
                json.dump(lock_data, f)
        except Exception as e:
            self.logger.error(f"Error saving lock state: {str(e)}")

    def __init__(self, mt5_login=None, mt5_password=None, mt5_server=None, symbols=None, timeframes=None, lot_size=0.1, daily_max_profit=500, simulate=False, risk_percent=2.0, mt5_path=None):
        # Initialize trading lock state before other attributes
        self.trading_locked = False
        self.lock_reason = None
        
        # Add SureTrend tracking attributes
        self.suretrend_tracking = {
            symbol: {
                tf: {
                    'conditions_met': False,
                    'signal_type': None,  # 'buy' or 'sell'
                    'start_time': None,
                    'start_price': None,
                    'current_deviation': 0,
                    'ma_invalidated': False,
                    'duration': 0,
                    'conditions': {
                        'trend_aligned': False,
                        'momentum_confirmed': False,
                        'volatility_suitable': False,
                        'ma_alignment': False
                    }
                } for tf in (timeframes or [])
            } for symbol in (symbols or [])
        }
        
        # Create monitoring control attributes
        self.stop_monitoring = threading.Event()
        self.monitoring_thread = None
        
        # Continue with existing initialization
        self.mt5_login = mt5_login
        self.mt5_password = mt5_password
        self.mt5_server = mt5_server
        self.symbols = symbols or []
        self.timeframes = timeframes or []
        self.lot_size = lot_size
        self.daily_max_profit = daily_max_profit
        self.simulate = simulate
        self.risk_percent = risk_percent
        self.mt5_path = mt5_path
        
        self.mt5_connected = False
        self.mt5_account_info = None
        self.mt5_account_balance = 0
        self.mt5_account_equity = 0
        self.mt5_account_margin = 0
        self.mt5_account_free_margin = 0
        self.mt5_account_margin_level = 0
        self.mt5_account_margin_free = 0
        self.mt5_account_margin_level = 0
        self.mt5_account_margin_so = 0
        self.mt5_account_margin_so_call = 0
        self.mt5_account_margin_so_mode = 0
        self.mt5_account_margin_so_mode_text = ""
        self.mt5_account_margin_so_mode_color = ""
        self.mt5_account_margin_so_mode_text_color = ""
        self.mt5_account_margin_so_mode_bg_color = ""
        self.mt5_account_margin_so_mode_border_color = ""
        self.mt5_account_margin_so_mode_border_width = 0
        self.mt5_account_margin_so_mode_border_style = ""
        self.mt5_account_margin_so_mode_border_radius = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
#python start3.py --mt5-login 61339636 --mt5-password "Neema@#54" --mt5-server "Pepperstone-Demo" --symbols XAUUSD EURUSD US500 NAS100 USDJPY --timeframes M1 M5 M15 M30 H1 H4  --lot-size 0.2 --daily-max-profit 1000  --risk-percent 1.5
#python start3.py --mt5-login 61339636 --mt5-password "Neema@#54" --mt5-server "Pepperstone-Demo" --symbols XAUUSD --timeframes M1 M5 --lot-size 0.2 --daily-max-profit 1000  --risk-percent 1.5
import os
import sys
import time
import shutil
import json
import queue
import random
import logging
import warnings
import threading
import argparse
import subprocess
import MetaTrader5 as mt5
from datetime import datetime, timedelta
import pandas as pd
import numpy as np
import plotly.graph_objects as go
import re
import requests
import keyboard
import colorlog
import talib
import psutil
import atexit
from reportlab.lib import colors
from reportlab.lib.pagesizes import letter
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Image, Table, TableStyle
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from prompt_toolkit import PromptSession
from prompt_toolkit.completion import WordCompleter
from prompt_toolkit.history import InMemoryHistory
from concurrent.futures import ThreadPoolExecutor
import tempfile
import shutil
from tqdm import tqdm

warnings.filterwarnings("ignore", category=UserWarning, message="Pandas doesn't allow columns to be created via a new attribute name")

class TradingStrategy:
    def __init__(self, mt5_login=None, mt5_password=None, mt5_server=None, symbols=None, timeframes=None, lot_size=0.1, daily_max_profit=500, simulate=False, risk_percent=2.0, mt5_path=None):
        # Initialize trading lock state before other attributes
        self.trading_locked = False
        self.trading_lock_reason = ""
        # Setup logging first       
        self._setup_logging()
        self.simulate = False
        # Add drawdown tracking attributes
        self.balance_file = "daily_balance.json"
        self.max_drawdown_percent = 50  # 50% maximum drawdown
        self.initial_balance = None
        self.lowest_balance = None
        self.load_daily_balance()
        self.initialize_daily_balance()
        self.mt5_login = mt5_login or 61318849
        self.mt5_password = mt5_password or "Neema@#54"
        self.mt5_server = mt5_server or "Pepperstone-Demo"
            # Initialize status update thread
        self.status_update_interval = 1  # Update every second
        self.status_thread_running = True
        self.status_thread = threading.Thread(target=self.status_update_loop, daemon=True)
        self.status_thread.start()
        
        # Initialize mock trade manager
        self.mock_trade_manager = MockTradeManager(self)

        # Add market check intervals
        self.market_check_interval = 60  # Check market status every 60 seconds
        self.market_closed_sleep = 300   # Sleep for 5 minutes when market is closed

        self.ADMIN_PASSWORD = "TR@d3L3@d3r2025#"  # Complex password for admin override
        self.max_daily_loss = -500  # Set maximum daily loss in points (negative value)
        # Add lock file path
        self.lock_file = "trading_lock.json"
        # Load lock state from file
        self.load_lock_state()

        # Add report generation folder
        self.reports_folder = "trade_reports"
        os.makedirs(self.reports_folder, exist_ok=True)
        
        # Register Times New Roman font
        pdfmetrics.registerFont(TTFont('Times-Roman', 'times.ttf'))
        self.accounts = {
            'default': {'login': self.mt5_login, 'password': self.mt5_password, 'server': self.mt5_server}
        }
        self.current_account = 'default'
        self.sync_enabled = False

        self.TELEGRAM_BOT_TOKEN = "7135089206:AAEmnAztKDkjXg5jM4dXbrjfF3dCvcwJ9Ow"
        self.TELEGRAM_CHAT_ID = "6178394807"
        self.telegram_offset = 0

        self.symbols = symbols if symbols is not None else ['XAUUSD']

        # Initialize symbol_info dictionary
        self.symbol_info = {symbol: {} for symbol in self.symbols}
        self.point = {symbol: None for symbol in self.symbols}

        # Define timeframe_configs before using it in parse_timeframe
        self.timeframe_configs = {
            'M1': mt5.TIMEFRAME_M1, 'M5': mt5.TIMEFRAME_M5, 'M15': mt5.TIMEFRAME_M15,
            'M30': mt5.TIMEFRAME_M30, 'H1': mt5.TIMEFRAME_H1, 'H4': mt5.TIMEFRAME_H4
        }
        # Now parse timeframes after timeframe_configs is defined
        self.timeframes = [self.parse_timeframe(tf) for tf in (timeframes or ['M1'])]

        self.timeframe_intervals = {
            mt5.TIMEFRAME_M1: 60, mt5.TIMEFRAME_M5: 300, mt5.TIMEFRAME_M15: 900,
            mt5.TIMEFRAME_M30: 1800, mt5.TIMEFRAME_H1: 3600, mt5.TIMEFRAME_H4: 14400
        }

        self.lot_size = lot_size
        self.deviation = 10

        self.lot_size = lot_size
        self.deviation = 10  # Adjusted to match second half
        self.max_retries = 3
        self.retry_delay = 5
        self.simulate = simulate
        self.risk_percent = risk_percent
        self.daily_max_profit = daily_max_profit

        self.primary_strategy_enabled = True
        self.suretrend_automation_enabled = False
        self.grid_trading_enabled = False
        self.grid_automation_enabled = False
        self.momentum_automation_enabled = False  # Removed momentum_enabled, using automation flag only

        self.grid_levels = 5
        self.grid_spacing = 10

        self.ma_configs = {
            tf: {'fast': 3 if tf in [mt5.TIMEFRAME_M1, mt5.TIMEFRAME_M5] else 5,
                 'slow': 8 if tf in [mt5.TIMEFRAME_M1, mt5.TIMEFRAME_M5] else 10,
                 'exit_fast': 5, 'exit_slow': 10}
            for tf in self.timeframes  # Changed to self.timeframes for consistency
        }
        self.macd_fast, self.macd_slow, self.macd_signal = 12, 26, 9
        self.momentum_period = 14
        self.psar_step, self.psar_max = 0.02, 0.2
        self.bollinger_period, self.bollinger_dev = 20, 2
        self.atr_period = 14

        self.breakeven_configs = {tf: 50.0 for tf in self.timeframes}
        self.trailing_stop_configs = {tf: 50.0 for tf in self.timeframes}
        self.trailing_delay_configs = {tf: 50.0 for tf in self.timeframes}
        self.signal_cooldown = 300  # 5 minutes default, matching second half
        self.initial_sl = 200  # Default SL in points, matching second half
        #self.initial_balance = 1000
        self.dynamic_management_enabled = False  # Aligned with second half default
        self.exit_signals_enabled = True
        self.use_m5_exit = False

        self.positions = {symbol: {} for symbol in self.symbols}
        self.daily_profit = {symbol: 0.0 for symbol in self.symbols}
        self.daily_trades = {symbol: [] for symbol in self.symbols}  # Simplified to list per symbol
        self.trade_history = {symbol: [] for symbol in self.symbols}
        self.grid_history = {symbol: [] for symbol in self.symbols}
        self.suretrend_history = {symbol: [] for symbol in self.symbols}
        self.momentum_history = {symbol: [] for symbol in self.symbols}
        self.trading_allowed = {symbol: True for symbol in self.symbols}
        self.last_check_times = {symbol: {tf: datetime.now() for tf in self.timeframes} for symbol in self.symbols}
        self.last_signal_times = {symbol: {tf: datetime.now() - timedelta(seconds=self.signal_cooldown) for tf in self.timeframes} for symbol in self.symbols}
        self.waiting_for_trade_confirmation = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.trade_confirmation_queue = queue.Queue()
        self.command_lock = threading.Lock()
        self.context_symbol = None
        self.threads = []
        self.symbol_terminal_threads = {}

        # Initialize ma_exit_enabled with both string and numeric timeframe keys
        self.ma_exit_enabled = {}
        for symbol in self.symbols:
            self.ma_exit_enabled[symbol] = {}
            for tf in self.timeframes:
                # Add numeric timeframe key
                self.ma_exit_enabled[symbol][tf] = False
                # Add string timeframe key
                tf_name = self.get_timeframe_name(tf)
                self.ma_exit_enabled[symbol][tf_name] = False
                # Special case for M5
                if tf_name == 'M5':
                    self.ma_exit_enabled[symbol][tf_name] = self.use_m5_exit

        self.volatility_check_enabled = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.psar_filter_enabled = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.psar_filter_timeframe = {symbol: {tf: mt5.TIMEFRAME_H1 for tf in self.timeframes} for symbol in self.symbols}
        self.data_cache = {symbol: {tf: {'df': None, 'last_time': None} for tf in self.timeframes} for symbol in self.symbols}
        self.suretrend_conditions_met = {symbol: {tf: {'buy': False, 'sell': False} for tf in self.timeframes} for symbol in self.symbols}
        self.trades_per_strategy = {symbol: {tf: {"primary": 0, "suretrend": 0, "grid": 0, "momentum": 0, "breakout_momentum": 0} for tf in self.timeframes} for symbol in self.symbols}

        self._setup_logging()
        self.load_trade_history()
        atexit.register(self.cleanup)
        keyboard.on_press_key("q", self.handle_exit)

        # Enhanced error handling settings
        self.max_consecutive_errors = 3
        self.error_cooldown = 60  # seconds
        self.last_error_time = None
        self.consecutive_errors = 0
        
        # Load saved Telegram offset
        self.load_telegram_offset()
        
        # Initialize connection status
        self.mt5_connected = False
        self.telegram_connected = False

        # Add semi-automated mode variables
        self.primary_strategy_semi_auto = False
        self.suretrend_semi_auto = False
        self.grid_semi_auto = False
        self.momentum_semi_auto = False

        # Add MT5 path to the initialization
        self.mt5_path = mt5_path or r"C:\Program Files\MetaTrader 5\terminal64.exe"

        # Add new sync-related attributes
        self.sync_interval = 1  # Sync every 1 second
        self.last_sync_time = datetime.now()
        self.last_known_positions = {symbol: {} for symbol in self.symbols}
        self.last_known_history = {symbol: set() for symbol in self.symbols}
        self.external_trade_defaults = {
            'sl_points': 200,  # Default SL in points
            'tp_ratio': 2.0,   # TP = SL * tp_ratio
            'timeframe': mt5.TIMEFRAME_M1  # Default timeframe for external trades
        }
        
        # Start continuous sync thread
        self.sync_thread = threading.Thread(target=self.continuous_sync_loop, daemon=True)
        self.sync_thread.start()

        # Add HFScalper strategy attributes
        self.hfscalper_enabled = False
        self.hfscalper_semi_auto = False
        self.hfscalper_min_momentum = 0.0001
        self.hfscalper_volatility_threshold = 1.5
        self.hfscalper_tp_points = 10
        self.hfscalper_psar_enabled = False
        self.hfscalper_psar_step = 0.02
        self.hfscalper_psar_max = 0.2
        self.hfscalper_history = {symbol: [] for symbol in (symbols or ['XAUUSD'])}

        self.breakout_momentum_enabled = False
        self.breakout_momentum_semi_auto = False
        self.breakout_momentum_history = {symbol: [] for symbol in self.symbols}
        self.rsi_period = 14  # RSI period for overbought/oversold detection
        self.rsi_overbought = 70
        self.rsi_oversold = 30
        self.consolidation_lookback = 20  # Lookback period for consolidation detection
        self.consolidation_threshold = 0.05  # BB width threshold for consolidation
        self.breakout_multiplier = 1.5  # TP multiplier based on consolidation range
        self.atr_multiplier_sl = 1.5  # SL multiplier based on ATR
        self.atr_multiplier_trailing = 1.0  # Trailing stop multiplier

        # Add new signal optimization attributes
        self.signal_optimization_enabled = False
        self.realtime_signals_enabled = True
        self.signal_quality_threshold = 0.7
        self.signal_interval = 1  # seconds
        self.signal_history = {symbol: {tf: [] for tf in self.timeframes} for symbol in self.symbols}
        self.signal_performance = {symbol: {tf: {'total': 0, 'successful': 0} for tf in self.timeframes} for symbol in self.symbols}
        self.signal_alerts_enabled = True
        self.signal_logging_enabled = True
        self.signal_filters = {
            'momentum_threshold': 0.0001,
            'volatility_threshold': 1.5,
            'min_confirmation_signals': 2,
            'min_signal_quality': 0.7
        }
        
        self.strategy_performance = {
            'primary': {'total': 0, 'successful': 0, 'profit': 0.0},
            'suretrend': {'total': 0, 'successful': 0, 'profit': 0.0},
            'grid': {'total': 0, 'successful': 0, 'profit': 0.0},
            'momentum': {'total': 0, 'successful': 0, 'profit': 0.0},
            'hfscalper': {'total': 0, 'successful': 0, 'profit': 0.0},
            'breakout_momentum': {'total': 0, 'successful': 0, 'profit': 0.0}
        }
        
        # Signal quality metrics
        self.signal_quality_metrics = {
            'accuracy': 0.0,
            'profit_factor': 0.0,
            'win_rate': 0.0,
            'avg_profit': 0.0,
            'avg_loss': 0.0
        }

        # Add SureTrend tracking attributes
        self.suretrend_tracking = {
            symbol: {
                tf: {
                    'conditions_met': False,
                    'signal_type': None,  # 'buy' or 'sell'
                    'start_time': None,
                    'start_price': None,
                    'current_deviation': 0,
                    'ma_invalidated': False,
                    'duration': 0,
                    'conditions': {
                        'trend_aligned': False,
                        'momentum_confirmed': False,
                        'volatility_suitable': False,
                        'ma_alignment': False
                    }
                } for tf in (timeframes or [])
            } for symbol in (symbols or [])
        }
        
        # Create an event to signal monitoring thread to stop
        self.stop_monitoring = threading.Event()
        
        # Create a thread for background monitoring
        self.monitoring_thread = None

    def _setup_logging(self):
        log_folder = "live_trading_logs"
        os.makedirs(log_folder, exist_ok=True)
        log_file = os.path.join(log_folder, f"trading_log_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log")
        
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)
        
        # Custom formatter using TerminalManager colors
        class ColoredFormatter(logging.Formatter):
            def format(self, record):
                if record.levelno >= logging.ERROR:
                    color = self.terminal.COLORS['red']
                elif record.levelno >= logging.WARNING:
                    color = self.terminal.COLORS['yellow']
                elif record.levelno >= logging.INFO:
                    color = self.terminal.COLORS['green']
                else:
                    color = self.terminal.COLORS['blue']
                
                record.msg = f"{color}{record.msg}{self.terminal.COLORS['reset']}"
                return super().format(record)
        
        # Set up handlers with the new formatter
        formatter = ColoredFormatter('%(asctime)s | %(levelname)s | %(message)s')
        
        # Console handler
        ch = logging.StreamHandler()
        ch.setFormatter(formatter)
        self.logger.addHandler(ch)
        
        # File handler
        fh = logging.FileHandler(log_file)
        fh.setFormatter(logging.Formatter('%(asctime)s | %(levelname)s | %(message)s'))
        self.logger.addHandler(fh)

    def update_status_line(self):
        """Update the status line with current system state."""
        try:
            # Get connection status
            mt5_status = "Connected" if self.mt5_connected else "Disconnected"
            telegram_status = "Connected" if self.telegram_connected else "Disconnected"
            
            # Get trade counts
            active_trades = sum(len(self.positions[s]) for s in self.symbols)
            mock_trades = len(self.mock_trade_manager.mock_trades)
            
            # Get profit
            daily_profit = sum(self.convert_to_points(self.daily_profit[s], s) for s in self.symbols)
            
            status = (
                f"Last Update: {datetime.now().strftime('%H:%M:%S')} | "
                f"MT5: {mt5_status} | Telegram: {telegram_status} | "
                f"Active Trades: {active_trades} | Mock Trades: {mock_trades} | "
                f"Daily Profit: {daily_profit:.1f} pts"
            )
            
            self.terminal.update_status(status)
        except Exception as e:
            self.logger.error(f"Error updating status line: {str(e)}")

    def parse_timeframe(self, tf_str):
        tf_str = tf_str.upper()
        return self.timeframe_configs.get(tf_str)

    def get_timeframe_name(self, timeframe):
        for name, value in self.timeframe_configs.items():
            if value == timeframe:
                return name
        return "Unknown"

    def get_telegram_updates(self):
        """Enhanced Telegram updates with proper offset handling and better timeout handling."""
        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/getUpdates"
        
        retry_count = 0
        while retry_count < self.max_retries:
            try:
                params = {
                    "offset": self.telegram_offset,
                    "timeout": 30,
                    "allowed_updates": ["message"]
                }
                
                # Increase timeout and add backoff strategy
                response = requests.get(url, params=params, timeout=60)
                response.raise_for_status()
                
                updates = response.json()
                if updates.get("ok") and "result" in updates:
                    if updates["result"]:
                        latest_update = max(update["update_id"] for update in updates["result"])
                        self.telegram_offset = latest_update + 1
                        self.save_telegram_offset()
                    return updates
                    
                time.sleep(1)
                
            except requests.exceptions.Timeout:
                retry_count += 1
                self.logger.warning(f"Telegram timeout (attempt {retry_count}/{self.max_retries}), retrying...")
                time.sleep(5 * retry_count)  # Progressive backoff
            except requests.exceptions.RequestException as e:
                retry_count += 1
                self.logger.error(f"Failed to get Telegram updates (attempt {retry_count}/{self.max_retries}): {str(e)}")
                if retry_count == self.max_retries:
                    time.sleep(60)
                    retry_count = 0
                else:
                    time.sleep(5 * retry_count)
        
        return None

    def save_telegram_offset(self):
        """Save Telegram offset to file."""
        try:
            with open("telegram_offset.txt", "w") as f:
                f.write(str(self.telegram_offset))
        except Exception as e:
            self.logger.error(f"Failed to save Telegram offset: {e}")

    def load_telegram_offset(self):
        """Load Telegram offset from file."""
        try:
            if os.path.exists("telegram_offset.txt"):
                with open("telegram_offset.txt", "r") as f:
                    self.telegram_offset = int(f.read().strip())
        except Exception as e:
            self.logger.error(f"Failed to load Telegram offset: {e}")

    def send_telegram_message(self, message, thread_id=None, chart_path=None, chat_id=None):
        """Enhanced Telegram message sending with better timeout handling"""
        if not self.TELEGRAM_BOT_TOKEN or not self.TELEGRAM_CHAT_ID:
            self.logger.warning("Telegram credentials not configured")
            return None

        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendMessage"
        max_length = 4096
        chat_id = chat_id or self.TELEGRAM_CHAT_ID
        
        # Format message
        formatted_message = f"> GC_Signals:\n{message}"
        formatted_message = formatted_message.replace('<', '&lt;').replace('>', '&gt;')
        
        # Split long messages
        if len(formatted_message) > max_length:
            parts = []
            current_part = "> GC_Signals:\n"
            for line in message.split('\n'):
                if len(current_part) + len(line) + 1 <= max_length:
                    current_part += line + '\n'
                else:
                    parts.append(current_part.strip())
                    current_part = f"> GC_Signals:\n{line}\n"
            if current_part:
                parts.append(current_part.strip())
        else:
            parts = [formatted_message]
        
        last_message_id = None
        for part in parts:
            retry_count = 0
            while retry_count < self.max_retries:
                try:
                    payload = {
                        "chat_id": chat_id,
                        "text": part,
                        "parse_mode": "HTML"
                    }
                    
                    if thread_id and not last_message_id:
                        payload["reply_to_message_id"] = thread_id
                    elif last_message_id:
                        payload["reply_to_message_id"] = last_message_id

                    response = requests.post(url, json=payload, timeout=30)  # Increased timeout
                    response.raise_for_status()
                    
                    result = response.json()
                    if not result.get("ok"):
                        raise Exception(f"Telegram API error: {result.get('description')}")
                        
                    last_message_id = result.get("result", {}).get("message_id")
                    
                    # Send chart if available
                    if chart_path and last_message_id and part == parts[-1]:
                        try:
                            with open(chart_path, 'rb') as chart_file:
                                files = {'photo': chart_file}
                                photo_url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendPhoto"
                                photo_response = requests.post(
                                    photo_url,
                                    data={"chat_id": chat_id, "reply_to_message_id": last_message_id},
                                    files=files,
                                    timeout=30  # Increased timeout
                                )
                                photo_response.raise_for_status()
                        except Exception as e:
                            self.logger.error(f"Failed to send chart: {e}")
                    
                    break
                    
                except Exception as e:
                    retry_count += 1
                    self.logger.error(f"Failed to send Telegram message (attempt {retry_count}/{self.max_retries}): {e}")
                    if retry_count == self.max_retries:
                        return None
                    time.sleep(5 * retry_count)  # Progressive backoff
        
        return last_message_id

    def load_trade_history(self):
        for symbol in self.symbols:
            for filename, history_dict in [
                (f"trade_history_{symbol}.json", self.trade_history),
                (f"grid_history_{symbol}.json", self.grid_history),
                (f"suretrend_history_{symbol}.json", self.suretrend_history),
                (f"momentum_history_{symbol}.json", self.momentum_history)
            ]:
                if os.path.exists(filename):
                    with open(filename, 'r') as f:
                        try:
                            history_dict[symbol] = json.load(f)
                            self.logger.info(f"[{symbol}] Loaded {len(history_dict[symbol])} trades from {filename}")
                        except json.JSONDecodeError:
                            self.logger.error(f"[{symbol}] Failed to load {filename}")

    def save_trade_history(self):
        for symbol in self.symbols:
            for filename, history_dict in [
                (f"trade_history_{symbol}.json", self.trade_history),
                (f"grid_history_{symbol}.json", self.grid_history),
                (f"suretrend_history_{symbol}.json", self.suretrend_history),
                (f"momentum_history_{symbol}.json", self.momentum_history)
            ]:
                with open(filename, 'w') as f:
                    json.dump(history_dict[symbol], f, default=str)

    def cleanup(self):
        self.logger.info("Cleaning up...")
        try:
            # Stop status thread
            self.status_thread_running = False
            if hasattr(self, 'status_thread'):
                self.status_thread.join(timeout=2)
            
            # Existing cleanup code...
            with self.command_lock:
                for symbol in self.symbols:
                    for position in list(self.positions[symbol].values()):
                        self.close_position(position, "System shutdown")
                self.save_trade_history()
                
            # Ensure proper MT5 shutdown
            if mt5.terminal_info():
                mt5.shutdown()
                
            # Additional cleanup for background terminal
            try:
                subprocess.run(['taskkill', '/F', '/IM', 'terminal64.exe'], capture_output=True)
            except Exception as e:
                self.logger.warning(f"Failed to force close MT5 terminal: {e}")
        except Exception as e:
            self.logger.error(f"Error during cleanup: {e}")

    def handle_exit(self, e):
        if e.name == 'q':
            self.cleanup()
            os._exit(0)

    def ensure_mt5_connection(self):
        """Enhanced MT5 connection handling with better retry logic"""
        if self.simulate:
            return True

        try:
            # First check if we're already connected
            if mt5.terminal_info() and mt5.account_info():
                return True

            # If not connected, try to initialize
            if not mt5.initialize():
                # Kill any existing MT5 processes first
                try:
                    import subprocess
                    import psutil
                    for proc in psutil.process_iter(['pid', 'name']):
                        try:
                            if proc.info['name'].lower() in ['terminal64.exe', 'metatrader.exe', 'metaeditor64.exe']:
                                subprocess.run(['taskkill', '/F', '/PID', str(proc.info['pid'])], capture_output=True)
                        except (psutil.NoSuchProcess, psutil.AccessDenied):
                            continue
                    time.sleep(2)  # Give time for processes to terminate
                except Exception as e:
                    self.logger.warning(f"Failed to kill existing MT5 processes: {e}")

                # Create a temporary directory for MT5 data
                temp_dir = tempfile.mkdtemp(prefix="mt5_temp_")
                self.logger.info(f"Created temporary directory for MT5: {temp_dir}")

                # Initialize with retries
                for attempt in range(3):
                    try:
                        initialized = mt5.initialize(
                            path=self.mt5_path,
                            login=self.mt5_login,
                            password=self.mt5_password,
                            server=self.mt5_server,
                            portable=True,
                            timeout=60000,
                            config={
                                "show": False,
                                "autoclose": True,
                                "silent": True
                            }
                        )

                        if initialized:
                            # Verify connection
                            if not mt5.account_info():
                                raise Exception("Failed to get account info after initialization")
                            
                            # Initialize symbols
                            for symbol in self.symbols:
                                if not mt5.symbol_select(symbol, True):
                                    raise Exception(f"Failed to select symbol {symbol}")
                                
                                symbol_info = mt5.symbol_info(symbol)
                                if not symbol_info:
                                    raise Exception(f"Failed to get symbol info for {symbol}")
                                
                                self.point[symbol] = symbol_info.point
                                self.symbol_info[symbol] = {
                                    'digits': symbol_info.digits,
                                    'trade_contract_size': symbol_info.trade_contract_size,
                                    'volume_min': symbol_info.volume_min,
                                    'volume_max': symbol_info.volume_max,
                                    'volume_step': symbol_info.volume_step
                                }
                            
                            self.mt5_connected = True
                            return True

                        error = mt5.last_error()
                        if attempt < 2:
                            self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed: {error}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {attempt + 1} attempts: {error}")
                            return False

                    except Exception as e:
                        if attempt < 2:
                            self.logger.warning(f"MT5 initialization error (attempt {attempt + 1}): {str(e)}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {attempt + 1} attempts with error: {str(e)}")
                            return False

            return False

        except Exception as e:
            self.logger.error(f"Error in ensure_mt5_connection: {str(e)}")
            return False

    def initialize_mt5(self):
        """Initialize MT5 connection and point values for all symbols."""
        # Initialize self.point as a dictionary if not already
        if not hasattr(self, 'point') or not isinstance(self.point, dict):
            self.point = {}
    
        if self.simulate:
            # Initialize point values for simulation mode
            for symbol in self.symbols:
                self.point[symbol] = 0.01 if symbol != "XAUUSD" else 0.01
            self.logger.info("Running in simulation mode; MT5 not initialized.")
            return True
    
        try:
            # First, ensure MT5 is completely shut down
            if mt5.terminal_info():
                mt5.shutdown()
            
            # Force kill any existing MT5 processes
            try:
                import subprocess
                import psutil
                
                # Kill terminal64.exe processes
                for proc in psutil.process_iter(['pid', 'name']):
                    try:
                        if proc.info['name'].lower() in ['terminal64.exe', 'metatrader.exe', 'metaeditor64.exe']:
                            subprocess.run(['taskkill', '/F', '/PID', str(proc.info['pid'])], capture_output=True)
                    except (psutil.NoSuchProcess, psutil.AccessDenied):
                        continue
                
                time.sleep(2)  # Give time for processes to terminate
            except Exception as e:
                self.logger.warning(f"Failed to kill existing MT5 processes: {e}")
    
            # Create a temporary directory for MT5 data
            import tempfile
            import shutil
            temp_dir = tempfile.mkdtemp(prefix="mt5_temp_")
            self.logger.info(f"Created temporary directory for MT5: {temp_dir}")
    
            # Initialize MT5 with retries
            max_retries = 3
            for attempt in range(max_retries):
                try:
                    # Initialize with minimal settings first
                    initialized = mt5.initialize(
                        path=self.mt5_path,
                        login=self.mt5_login,
                        password=self.mt5_password,
                        server=self.mt5_server,
                        portable=True,
                        timeout=60000,
                        config={
                            "show": False,
                            "autoclose": True,
                            "silent": True
                        }
                    )
    
                    if not initialized:
                        error = mt5.last_error()
                        if attempt < max_retries - 1:
                            self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed: {error}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {max_retries} attempts: {error}")
                            shutil.rmtree(temp_dir, ignore_errors=True)
                            return False
    
                    # Verify connection and login
                    account_info = mt5.account_info()
                    if not account_info:
                        self.logger.error("Failed to get account info")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
                    # Verify trading is enabled
                    terminal = mt5.terminal_info()
                    if not terminal:
                        self.logger.error("Failed to get terminal info")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
                    if not terminal.trade_allowed:
                        self.logger.warning("AutoTrading is disabled, attempting to enable...")
                        # We'll continue anyway as it might be enabled later
    
                    self.logger.info(f"Successfully connected to account {account_info.login} on {self.mt5_server}")
                    self.logger.info(f"Balance: ${account_info.balance:.2f}, Equity: ${account_info.equity:.2f}")
                    self.logger.info(f"Margin Level: {account_info.margin_level:.2f}%")
                    
                    # Initialize symbols
                    for symbol in self.symbols:
                        if not mt5.symbol_select(symbol, True):
                            self.logger.error(f"Failed to select symbol {symbol}")
                            continue
                        
                        symbol_info = mt5.symbol_info(symbol)
                        if symbol_info:
                            # Store point value in dictionary
                            self.point[symbol] = symbol_info.point
                            self.symbol_info[symbol] = {
                                'digits': symbol_info.digits,
                                'trade_contract_size': symbol_info.trade_contract_size,
                                'volume_min': symbol_info.volume_min,
                                'volume_max': symbol_info.volume_max,
                                'volume_step': symbol_info.volume_step
                            }
                            self.logger.info(f"Initialized {symbol}: Point={symbol_info.point}, "
                                           f"Digits={symbol_info.digits}, "
                                           f"Contract Size={symbol_info.trade_contract_size}")
                        else:
                            self.logger.error(f"Failed to get symbol info for {symbol}")
                            self.point[symbol] = 0.01  # Fallback point value
                            continue  # Try to continue with other symbols
    
                    # Validate that all symbols have point values
                    for symbol in self.symbols:
                        if symbol not in self.point:
                            self.logger.warning(f"No point value set for {symbol}, using fallback value 0.01")
                            self.point[symbol] = 0.01
    
                    self.mt5_connected = True
                    return True
    
                except Exception as e:
                    if attempt < max_retries - 1:
                        self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed with error: {str(e)}. Retrying...")
                        time.sleep(5)
                    else:
                        self.logger.error(f"MT5 initialization failed after {max_retries} attempts with error: {str(e)}")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
        except Exception as e:
            self.logger.error(f"Error in initialize_mt5: {str(e)}")
            return False
        finally:
            # Clean up temporary directory if it exists
            try:
                if 'temp_dir' in locals():
                    shutil.rmtree(temp_dir, ignore_errors=True)
            except Exception as e:
                self.logger.warning(f"Failed to clean up temporary directory: {e}")

    def add_account(self, name, login, password, server):
        if name in self.accounts:
            self.logger.warning(f"Account '{name}' already exists.")
            return False
        self.accounts[name] = {"login": int(login), "password": password, "server": server}
        self.logger.info(f"Added account '{name}' with login {login} and server {server}.")
        # If no current account is set, make this the default and initialize
        if not self.current_account:
            self.current_account = name
            self.mt5_login = login
            self.mt5_password = password
            self.mt5_server = server
            if not self.initialize_mt5():
                self.logger.error(f"Failed to initialize MT5 with new account '{name}'.")
                del self.accounts[name]
                return False
        return True

    def load_daily_balance(self):
        """Load daily balance tracking information from file."""
        try:
            if os.path.exists(self.balance_file):
                with open(self.balance_file, 'r') as f:
                    data = json.load(f)
                    # Check if data is from today
                    saved_date = datetime.strptime(data.get('date', ''), '%Y-%m-%d').date()
                    if saved_date == datetime.now().date():
                        self.initial_balance = data.get('initial_balance')
                        self.lowest_balance = data.get('lowest_balance')
                        self.trading_locked = data.get('trading_locked', False)
                        self.trading_lock_reason = data.get('lock_reason', '')
                    else:
                        # New day, get fresh balance
                        self.initialize_daily_balance()
            else:
                self.initialize_daily_balance()
        except Exception as e:
            self.logger.error(f"Error loading daily balance: {str(e)}")
            self.initialize_daily_balance()


    def initialize_daily_balance(self):
        """Initialize daily balance tracking with current MT5 account balance."""
        try:
            if not self.simulate:
                # First ensure MT5 connection
                if not self.ensure_mt5_connection():
                    self.logger.error("Failed to connect to MT5 for balance initialization")
                    return
    
                # Get actual account balance from MT5
                account_info = mt5.account_info()
                if account_info:
                    self.initial_balance = account_info.balance
                    self.lowest_balance = account_info.balance
                    self.trading_locked = False
                    self.trading_lock_reason = ""
                    self.logger.info(f"Initialized daily balance tracking with MT5 balance: ${self.initial_balance:.2f}")
                else:
                    # Log error and exit if can't get balance
                    self.logger.error("Failed to get MT5 account balance")
                    return
            else:
                # For simulation, get actual balance first
                account_info = mt5.account_info()
                if account_info:
                    self.initial_balance = account_info.balance
                else:
                    self.initial_balance = 146.52  # Use current actual balance as fallback
                self.lowest_balance = self.initial_balance
                self.trading_locked = False
                self.trading_lock_reason = ""
    
            self.save_daily_balance()
    
        except Exception as e:
            self.logger.error(f"Error initializing daily balance: {str(e)}")
            # Do not set any default values, just log error and return
            return

    def save_daily_balance(self):
        """Save daily balance tracking information to file."""
        try:
            data = {
                'date': datetime.now().strftime('%Y-%m-%d'),
                'initial_balance': self.initial_balance,
                'lowest_balance': self.lowest_balance,
                'trading_locked': self.trading_locked,
                'lock_reason': self.trading_lock_reason
            }
            with open(self.balance_file, 'w') as f:
                json.dump(data, f)
        except Exception as e:
            self.logger.error(f"Error saving daily balance: {str(e)}")

    def check_drawdown(self):
        """Check if current drawdown exceeds maximum allowed percentage."""
        try:
            if not self.initial_balance:
                return False

            current_balance = 0
            if not self.simulate:
                # Get fresh balance from MT5
                account_info = mt5.account_info()
                if account_info:
                    current_balance = account_info.balance
                else:
                    self.logger.error("Failed to get current MT5 balance")
                    return False
            else:
                # In simulation mode, calculate from tracked profits
                current_balance = self.initial_balance + sum(self.daily_profit.values())

            # Skip drawdown check if initial balance is zero or null
            if not self.initial_balance:
                return False

            # Update lowest balance if current is lower
            if self.lowest_balance is None or current_balance < self.lowest_balance:
                self.lowest_balance = current_balance
                self.save_daily_balance()

            # Calculate drawdown percentage using actual values
            drawdown_percent = ((self.initial_balance - current_balance) / self.initial_balance) * 100 if self.initial_balance > 0 else 0

            if drawdown_percent >= self.max_drawdown_percent:
                message = (
                    f"⚠️ MAXIMUM DRAWDOWN REACHED ⚠️\n"
                    f"Initial Balance: ${self.initial_balance:.2f}\n"
                    f"Current Balance: ${current_balance:.2f}\n"
                    f"Drawdown: {drawdown_percent:.2f}%\n"
                    f"Trading will be locked for the rest of the day."
                )
                self.lock_trading(message)
                self.save_daily_balance()
                return True

            return False

        except Exception as e:
            self.logger.error(f"Error checking drawdown: {str(e)}")
            return False

    def switch_account(self, name):
        if name not in self.accounts:
            self.logger.error(f"Account '{name}' not found.")
            return False
        if name == self.current_account:
            self.logger.info(f"Already on account '{name}'.")
            return True
        
        # Store current positions before switching
        current_positions = {symbol: dict(self.positions[symbol]) for symbol in self.symbols}
        
        # Update current account details
        self.current_account = name
        self.mt5_login = self.accounts[name]["login"]
        self.mt5_password = self.accounts[name]["password"]
        self.mt5_server = self.accounts[name]["server"]
        
        # Reinitialize MT5 with new account
        if not self.initialize_mt5():
            self.logger.error(f"Failed to switch to account '{name}'.")
            return False
        
        # Restore positions or sync with new account
        self.positions = {symbol: {} for symbol in self.symbols}  # Reset positions
        self.sync_positions_with_mt5()
        
        self.logger.info(f"Switched to account '{name}' successfully.")
        return True

    def sync_positions_with_mt5(self):
        """Enhanced synchronization with MT5 including proper script trade tracking."""
        if self.simulate:
            return True

        try:
            # Get all current MT5 positions
            mt5_positions = mt5.positions_get()
            if mt5_positions is None:
                self.logger.error("Failed to get positions from MT5")
                return False
                
            mt5_tickets = {pos.ticket for pos in mt5_positions}
            
            # Use a timeout context for the lock
            if not self.command_lock.acquire(timeout=5):
                self.logger.error("Failed to acquire lock for position synchronization")
                return False
                
            try:
                for symbol in self.symbols:
                    # Check for positions that exist in our tracking but not in MT5
                    for ticket in list(self.positions[symbol].keys()):
                        if ticket not in mt5_tickets:
                            # Position was closed externally
                            position = self.positions[symbol][ticket]
                            self.logger.info(f"[{symbol}] Position {ticket} closed externally, updating records")
                            
                            # Calculate final profit if possible
                            profit_points = 0
                            if mt5_positions:
                                for mt5_pos in mt5_positions:
                                    if mt5_pos.ticket == ticket:
                                        profit_points = self.convert_to_points(mt5_pos.profit, symbol)
                                        break
                            
                            # Update trade history
                            self.update_trade_history_on_close(ticket, symbol, profit_points, "Closed externally")
                            
                            # Remove from tracking
                            del self.positions[symbol][ticket]
                    
                    # Add any new positions from MT5 that we're not tracking
                    for pos in mt5_positions:
                        if pos.symbol == symbol and pos.ticket not in self.positions[symbol]:
                            # Check if this is a script-placed trade based on comment
                            is_script_trade = pos.comment and pos.comment.startswith("GC_Signals_")
                            strategy = pos.comment.replace("GC_Signals_", "") if is_script_trade else "external"
                            
                            if not is_script_trade:
                                # This is an external trade - add it with external trade handling
                                self.handle_external_trade(pos)
                            else:
                                # This is our trade that somehow got disconnected - restore it
                                self.positions[symbol][pos.ticket] = {
                                    'ticket': pos.ticket,
                                    'type': pos.type,
                                    'entry_price': pos.price_open,
                                    'lot_size': pos.volume,
                                    'sl': pos.sl,
                                    'tp': pos.tp,
                                    'timeframe': mt5.TIMEFRAME_M1,  # Default to M1 if unknown
                                    'strategy': strategy,
                                    'entry_time': datetime.fromtimestamp(pos.time).strftime('%Y-%m-%d %H:%M:%S.%f'),
                                    'signal_time': datetime.fromtimestamp(pos.time).strftime('%Y-%m-%d %H:%M:%S.%f'),
                                    'breakeven_triggered': False,
                                    'trailing_active': False,
                                    'thread_id': None,
                                    'reason': strategy,
                                    'comments': pos.comment,
                                    'symbol': symbol,
                                    'profit': pos.profit,
                                    'script_placed': True
                                }
                                self.logger.info(f"[{symbol}] Restored script-placed trade {pos.ticket}")
            finally:
                self.command_lock.release()
            
            self.save_trade_history()
            return True
            
        except Exception as e:
            self.logger.error(f"Error in sync_positions_with_mt5: {str(e)}")
            if self.command_lock.locked():
                self.command_lock.release()
            return False

    def prompt_position_params(self, position):
        """Prompt for position parameters after trade entry."""
        symbol = position['symbol']
        point = self.point[symbol]  # Get point value directly from self.point dictionary
        
        # Calculate current parameters in points
        current_sl_points = abs(position['sl'] - position['entry_price']) / point if position['sl'] else 0
        current_tp_points = abs(position['tp'] - position['entry_price']) / point if position['tp'] else 0
        
        message = (
            f"🔧 Position Parameters Required:\n"
            f"Ticket: {position['ticket']}\n"
            f"Symbol: {symbol}\n"
            f"Entry: {position['entry_price']:.5f}\n"
            f"Current Settings:\n"
            f"- SL: {current_sl_points:.0f} points\n"
            f"- TP: {current_tp_points:.0f} points\n"
            f"- Trail Stop: {self.trailing_stop_configs[position['timeframe']]:.1f} points\n"
            f"- Trail Delay: {self.trailing_delay_configs[position['timeframe']]:.1f} points\n"
            f"- MA Exit: {'Enabled' if self.ma_exit_enabled[symbol][position['timeframe']] else 'Disabled'}\n\n"
            f"Reply with: setparams <ticket> <sl_points> <tp_points> <trail_stop> <trail_delay> <ma_exit>\n"
            f"Example: setparams {position['ticket']} 100 200 20 50 1\n"
            f"(Use 0 for default values, 1/0 for ma_exit enable/disable)"
        )
        
        # Send to both interfaces
        self.send_telegram_message(message)
        print(f"\n{message}")
        position['waiting_params'] = True

    def handle_position_params(self, cmd_parts):
        """Handle the setparams command for position parameters."""
        try:
            if len(cmd_parts) != 7:
                return "Invalid parameters. Usage: setparams <ticket> <sl_points> <tp_points> <trail_stop> <trail_delay> <ma_exit>"
            
            _, ticket, sl_points, tp_points, trail_stop, trail_delay, ma_exit = cmd_parts
            ticket = int(ticket)
            
            # Find position
            position = None
            symbol = None
            for sym in self.symbols:
                if ticket in self.positions[sym]:
                    position = self.positions[sym][ticket]
                    symbol = sym
                    break
            
            if not position:
                return f"Position with ticket {ticket} not found."
            
            if not position.get('waiting_params', False):
                return f"Position {ticket} is not waiting for parameter settings."
            
            # Get symbol point value
            point = self.point[symbol]
            
            # Calculate actual SL/TP prices based on points
            sl_points = float(sl_points)
            tp_points = float(tp_points)
            
            if sl_points > 0:
                sl = (position['entry_price'] - sl_points * point) if position['type'] == mt5.ORDER_TYPE_BUY else \
                    (position['entry_price'] + sl_points * point)
            else:
                sl = position['sl']
                
            if tp_points > 0:
                tp = (position['entry_price'] + tp_points * point) if position['type'] == mt5.ORDER_TYPE_BUY else \
                    (position['entry_price'] - tp_points * point)
            else:
                tp = position['tp']
            
            trail_stop = float(trail_stop) if float(trail_stop) != 0 else self.trailing_stop_configs[position['timeframe']]
            trail_delay = float(trail_delay) if float(trail_delay) != 0 else self.trailing_delay_configs[position['timeframe']]
            ma_exit = bool(int(ma_exit))
            
            # Apply parameters
            success = self.modify_position(position, sl=sl, tp=tp)
            if not success:
                return "Failed to modify position parameters"
                
            self.trailing_stop_configs[position['timeframe']] = trail_stop
            self.trailing_delay_configs[position['timeframe']] = trail_delay
            self.ma_exit_enabled[symbol][position['timeframe']] = ma_exit
            
            position['waiting_params'] = False
            
            return (f"Parameters set for ticket {ticket}:\n"
                    f"SL: {sl_points:.0f} points (Price: {sl:.5f})\n"
                    f"TP: {tp_points:.0f} points (Price: {tp:.5f})\n"
                    f"Trail Stop: {trail_stop} points\n"
                    f"Trail Delay: {trail_delay} points\n"
                    f"MA Exit: {'Enabled' if ma_exit else 'Disabled'}")
                    
        except Exception as e:
            return f"Error setting parameters: {str(e)}"

    def generate_trade_report(self, ticket=None, symbol=None, daily=False):
        """Generate detailed trade report in PDF format with embedded charts including Parabolic SAR and MACD using TA-Lib."""
        try:
            # Create PDF document
            filename = f"trade_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.pdf"
            filepath = os.path.join(self.reports_folder, filename)
            
            doc = SimpleDocTemplate(filepath, pagesize=letter)
            story = []
            
            # Get trades to report
            trades = []
            title = ""
            if ticket:
                # For ticket-specific report
                title = f"TRADE REPORT TICKET No. {ticket}"
                for sym in self.symbols:
                    # Check current open positions
                    if ticket in self.positions[sym]:
                        position = self.positions[sym][ticket]
                        trade = {
                            'ticket': position['ticket'],
                            'type': "BUY" if position['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                            'entry_price': position['entry_price'],
                            'close_price': None,
                            'sl': position['sl'],
                            'tp': position['tp'],
                            'lot_size': position['lot_size'],
                            'entry_time': position['entry_time'],
                            'close_time': None,
                            'symbol': sym,
                            'timeframe': position['timeframe'],
                            'profit': position['profit'],
                            'reason': position.get('reason', 'Manual/External Trade'),
                            'comments': position.get('comments', ''),
                            'status': 'open'
                        }
                        trades.append(trade)
                    
                    # Check all history categories
                    for history_list in [
                        self.trade_history[sym],
                        self.grid_history[sym],
                        self.suretrend_history[sym],
                        self.momentum_history[sym]
                    ]:
                        trades.extend([t for t in history_list if t.get('ticket') == ticket])
                    
                    # Get MT5 history for the ticket
                    if not self.simulate:
                        mt5_history = mt5.history_deals_get(ticket=ticket)
                        if mt5_history:
                            for deal in mt5_history:
                                if not any(t.get('ticket') == deal.ticket for t in trades):
                                    trades.append({
                                        'ticket': deal.ticket,
                                        'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                        'entry_price': deal.price,
                                        'close_price': deal.price,
                                        'sl': 0.0,
                                        'tp': 0.0,
                                        'lot_size': deal.volume,
                                        'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'symbol': deal.symbol,
                                        'timeframe': 'M1',
                                        'profit': deal.profit,
                                        'reason': 'External MT5 Trade',
                                        'comments': deal.comment,
                                        'status': 'closed'
                                    })
                    
            elif symbol:
                # For symbol-specific report
                title = f"TRADE REPORT {symbol}"
                # Include current open positions
                for pos in self.positions[symbol].values():
                    trades.append({
                        'ticket': pos['ticket'],
                        'type': "BUY" if pos['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                        'entry_price': pos['entry_price'],
                        'close_price': None,
                        'sl': pos['sl'],
                        'tp': pos['tp'],
                        'lot_size': pos['lot_size'],
                        'entry_time': pos['entry_time'],
                        'close_time': None,
                        'symbol': symbol,
                        'timeframe': pos['timeframe'],
                        'profit': pos['profit'],
                        'reason': pos.get('reason', 'Manual/External Trade'),
                        'comments': pos.get('comments', ''),
                        'status': 'open'
                    })
                
                # Add all historical trades
                trades.extend(self.trade_history[symbol])
                trades.extend(self.grid_history[symbol])
                trades.extend(self.suretrend_history[symbol])
                trades.extend(self.momentum_history[symbol])
                
                # Get MT5 history for the symbol
                if not self.simulate:
                    mt5_history = mt5.history_deals_get(
                        datetime.now() - timedelta(days=7),
                        datetime.now(),
                        symbol=symbol
                    )
                    if mt5_history:
                        for deal in mt5_history:
                            if not any(t.get('ticket') == deal.ticket for t in trades):
                                trades.append({
                                    'ticket': deal.ticket,
                                    'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                    'entry_price': deal.price,
                                    'close_price': deal.price,
                                    'sl': 0.0,
                                    'tp': 0.0,
                                    'lot_size': deal.volume,
                                    'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                    'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                    'symbol': symbol,
                                    'timeframe': 'M1',
                                    'profit': deal.profit,
                                    'reason': 'External MT5 Trade',
                                    'comments': deal.comment,
                                    'status': 'closed'
                                })
                    
            elif daily:
                # For daily report
                title = f"DAILY TRADE REPORT {datetime.now().strftime('%Y-%m-%d')}"
                today = datetime.now().date()
                
                for sym in self.symbols:
                    # Include current open positions opened today
                    for pos in self.positions[sym].values():
                        if self.parse_trade_time(pos['entry_time']).date() == today:
                            trades.append({
                                'ticket': pos['ticket'],
                                'type': "BUY" if pos['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                                'entry_price': pos['entry_price'],
                                'close_price': None,
                                'sl': pos['sl'],
                                'tp': pos['tp'],
                                'lot_size': pos['lot_size'],
                                'entry_time': pos['entry_time'],
                                'close_time': None,
                                'symbol': sym,
                                'timeframe': pos['timeframe'],
                                'profit': pos['profit'],
                                'reason': pos.get('reason', 'Manual/External Trade'),
                                'comments': pos.get('comments', ''),
                                'status': 'open'
                            })
                    
                    # Add all historical trades from today
                    for history_list in [
                        self.trade_history[sym],
                        self.grid_history[sym],
                        self.suretrend_history[sym],
                        self.momentum_history[sym]
                    ]:
                        trades.extend([t for t in history_list 
                                     if self.parse_trade_time(t.get('entry_time', '')).date() == today])
                    
                    # Get today's MT5 history
                    if not self.simulate:
                        today_start = datetime.combine(today, datetime.min.time())
                        mt5_history = mt5.history_deals_get(today_start, datetime.now(), symbol=sym)
                        if mt5_history:
                            for deal in mt5_history:
                                if not any(t.get('ticket') == deal.ticket for t in trades):
                                    trades.append({
                                        'ticket': deal.ticket,
                                        'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                        'entry_price': deal.price,
                                        'close_price': deal.price,
                                        'sl': 0.0,
                                        'tp': 0.0,
                                        'lot_size': deal.volume,
                                        'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'symbol': sym,
                                        'timeframe': 'M1',
                                        'profit': deal.profit,
                                        'reason': 'External MT5 Trade',
                                        'comments': deal.comment,
                                        'status': 'closed'
                                    })
            
            if not trades:
                return "No trades found for the specified criteria."
        
            # Add title
            story.append(Paragraph(title, ParagraphStyle('Title', fontSize=14, spaceAfter=20)))
            
            # Process trades
            for trade in trades:
                try:
                    # Get timeframe (handle both string and numeric formats)
                    trade_tf = trade.get('timeframe')
                    if isinstance(trade_tf, str):
                        timeframe = self.parse_timeframe(trade_tf)
                        tf_name = trade_tf
                    else:
                        timeframe = trade_tf
                        tf_name = self.get_timeframe_name(trade_tf)
                    
                    if not timeframe:
                        # If timeframe is invalid or missing, try to determine from trade history
                        time_diff = None
                        if trade.get('entry_time') and trade.get('close_time'):
                            entry = self.parse_trade_time(trade['entry_time'])
                            close = self.parse_trade_time(trade['close_time'])
                            time_diff = (close - entry).total_seconds()
                        
                        # Assign appropriate timeframe based on trade duration
                        if time_diff:
                            if time_diff <= 3600:  # 1 hour or less
                                timeframe = mt5.TIMEFRAME_M5
                                tf_name = 'M5'
                            elif time_diff <= 14400:  # 4 hours or less
                                timeframe = mt5.TIMEFRAME_M15
                                tf_name = 'M15'
                            else:
                                timeframe = mt5.TIMEFRAME_H1
                                tf_name = 'H1'
                        else:
                            # Default to M5 if can't determine
                            timeframe = mt5.TIMEFRAME_M5
                            tf_name = 'M5'
                    
                    # Trade placed details
                    trade_type = "Buy" if trade.get('type') == "BUY" else "Sell"
                    entry_details = (
                        f"Trade Placed: {trade_type} {trade.get('symbol', '')} {tf_name} "
                        f"Ticket no{trade.get('ticket', '')} placed {trade.get('entry_price', 0.0):.5f} "
                        f"due to {trade.get('reason', 'N/A')}"
                    )
                    story.append(Paragraph(entry_details, ParagraphStyle('Normal', spaceBefore=10)))
                    
                    # Add chart for the trade
                    symbol = trade.get('symbol')
                    entry_time = self.parse_trade_time(trade.get('entry_time', ''))
                    
                    # Get historical data around the trade time with appropriate timeframe
                    df = self.get_rates(symbol, timeframe=timeframe)
                    if df is not None:
                        df = self.calculate_indicators(df, timeframe, symbol)
                        
                        # Calculate Parabolic SAR and MACD using TA-Lib
                        import talib
                        import numpy as np
                        
                        # Ensure sufficient data for indicators
                        if len(df) < 26:  # Minimum for MACD slow EMA
                            self.logger.warning(f"Insufficient data for indicators on {symbol} {tf_name}: {len(df)} rows")
                            story.append(Paragraph(f"Insufficient data for indicators for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Convert to NumPy arrays for TA-Lib
                        high = np.array(df['high'], dtype=float)
                        low = np.array(df['low'], dtype=float)
                        close = np.array(df['close'], dtype=float)
                        
                        # Parabolic SAR
                        df['sar'] = talib.SAR(high, low, acceleration=0.02, maximum=0.2)
                        
                        # MACD
                        macd, macd_signal, macd_hist = talib.MACD(
                            close,
                            fastperiod=12,
                            slowperiod=26,
                            signalperiod=9
                        )
                        df['macd'] = macd
                        df['macd_signal'] = macd_signal
                        df['macd_hist'] = macd_hist
                        
                        # Create figure with subplots (main chart + MACD)
                        from plotly.subplots import make_subplots
                        fig = make_subplots(
                            rows=2, cols=1,
                            row_heights=[0.7, 0.3],
                            shared_xaxes=True,
                            vertical_spacing=0.1,
                            subplot_titles=[f"{symbol} {tf_name} Trade Chart", "MACD"]
                        )
                        
                        # Add candlestick chart to main plot (row 1)
                        fig.add_trace(
                            go.Candlestick(
                                x=df['time'],
                                open=df['open'],
                                high=df['high'],
                                low=df['low'],
                                close=df['close'],
                                name='OHLC'
                            ),
                            row=1, col=1
                        )
                        
                        # Add moving averages to main plot
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['ma_fast'],
                                mode='lines',
                                name=f'MA {self.ma_configs[timeframe]["fast"]}',
                                line=dict(color='blue')
                            ),
                            row=1, col=1
                        )
                        
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['ma_slow'],
                                mode='lines',
                                name=f'MA {self.ma_configs[timeframe]["slow"]}',
                                line=dict(color='red')
                            ),
                            row=1, col=1
                        )
                        
                        # Add Parabolic SAR to main plot
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['sar'],
                                mode='markers',
                                name='Parabolic SAR',
                                marker=dict(symbol='circle', size=5, color='purple')
                            ),
                            row=1, col=1
                        )
                        
                        # Add entry and exit points to main plot
                        entry_price = trade.get('entry_price')
                        exit_price = trade.get('close_price')
                        
                        fig.add_hline(y=entry_price, line_dash="dash", line_color="blue", annotation_text="Entry", row=1)
                        if exit_price:
                            fig.add_hline(y=exit_price, line_dash="dash", line_color="red", annotation_text="Exit", row=1)
                        
                        # Add SL/TP lines if available to main plot
                        if trade.get('sl'):
                            fig.add_hline(y=trade['sl'], line_dash="dot", line_color="red", annotation_text="SL", row=1)
                        if trade.get('tp'):
                            fig.add_hline(y=trade['tp'], line_dash="dot", line_color="green", annotation_text="TP", row=1)
                        
                        # Add MACD to subplot (row 2)
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['macd'],
                                mode='lines',
                                name='MACD',
                                line=dict(color='blue')
                            ),
                            row=2, col=1
                        )
                        
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['macd_signal'],
                                mode='lines',
                                name='Signal',
                                line=dict(color='orange')
                            ),
                            row=2, col=1
                        )
                        
                        fig.add_trace(
                            go.Bar(
                                x=df['time'],
                                y=df['macd_hist'],
                                name='Histogram',
                                marker_color=df['macd_hist'].apply(lambda x: 'green' if x >= 0 else 'red')
                            ),
                            row=2, col=1
                        )
                        
                        # Add profit annotation to main plot
                        if trade.get('profit_points'):
                            fig.add_annotation(
                                x=df['time'].iloc[-1],
                                y=exit_price or df['close'].iloc[-1],
                                text=f"Profit: {trade.get('profit_points', 0):.2f} points",
                                showarrow=True,
                                arrowhead=1,
                                row=1, col=1
                            )
                        
                        # Update layout
                        fig.update_layout(
                            height=500,
                            margin=dict(l=50, r=50, t=50, b=50),
                            showlegend=True,
                            xaxis2=dict(title='Time'),
                            yaxis=dict(title='Price'),
                            yaxis2=dict(title='MACD')
                        )
                        
                        # Save chart as temporary image with absolute path
                        temp_chart = os.path.join(self.reports_folder, f"temp_chart_{trade.get('ticket')}.png")
                        try:
                            self.logger.debug(f"Attempting to write chart to {temp_chart}")
                            fig.write_image(temp_chart, engine="kaleido")
                            self.logger.debug(f"Chart written to {temp_chart}")
                        except Exception as e:
                            self.logger.error(f"Failed to write chart image {temp_chart}: {str(e)}")
                            story.append(Paragraph(f"Chart generation failed for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Verify file exists before adding to PDF
                        if not os.path.exists(temp_chart):
                            self.logger.error(f"Chart image {temp_chart} was not created.")
                            story.append(Paragraph(f"Chart missing for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Add chart to PDF
                        try:
                            img = Image(temp_chart)
                            img.drawHeight = 350
                            img.drawWidth = 500
                            story.append(img)
                            story.append(Spacer(1, 20))
                        except Exception as e:
                            self.logger.error(f"Failed to add chart {temp_chart} to PDF: {str(e)}")
                            story.append(Paragraph(f"Chart inclusion failed for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Clean up temporary file
                        try:
                            os.remove(temp_chart)
                            self.logger.debug(f"Deleted temporary chart {temp_chart}")
                        except Exception as e:
                            self.logger.warning(f"Failed to delete temporary chart {temp_chart}: {str(e)}")
                    
                    # Add SL/TP details
                    sl_tp_details = (
                        f"Initial SL: {trade.get('sl', 'N/A'):.5f}, "
                        f"TP: {trade.get('tp', 'N/A'):.5f}"
                    )
                    story.append(Paragraph(sl_tp_details, ParagraphStyle('Normal', leftIndent=20)))
                    
                    # Add close details if trade is closed
                    if trade.get('close_time'):
                        close_details = (
                            f"Trade Closed: The trade {trade_type} {trade.get('symbol', '')} {tf_name} "
                            f"Ticket no{trade.get('ticket', '')} was closed at {trade.get('close_time', '')} "
                            f"due to {trade.get('close_reason', 'N/A')}"
                        )
                        story.append(Paragraph(close_details, ParagraphStyle('Normal', spaceBefore=10)))
                    
                    story.append(Spacer(1, 20))
                    
                except Exception as e:
                    self.logger.error(f"Error processing trade {trade.get('ticket', 'unknown')}: {str(e)}")
                    continue
            
            # Build PDF
            doc.build(story)
            
            # Send report via Telegram if available
            if self.TELEGRAM_BOT_TOKEN and self.TELEGRAM_CHAT_ID:
                try:
                    with open(filepath, 'rb') as f:
                        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendDocument"
                        files = {'document': f}
                        data = {'chat_id': self.TELEGRAM_CHAT_ID}
                        response = requests.post(url, data=data, files=files)
                        if not response.json().get('ok'):
                            self.logger.error(f"Failed to send report via Telegram: {response.json()}")
                except Exception as e:
                    self.logger.error(f"Error sending report via Telegram: {str(e)}")
            
            return f"Report generated successfully: {filepath}"
            
        except Exception as e:
            self.logger.error(f"Error generating trade report: {str(e)}")
            return f"Failed to generate report: {str(e)}"
    
    def parse_trade_time(self, time_str):
        """Parse trade time string handling both formats with and without microseconds."""
        try:
            # Try parsing with microseconds
            return datetime.strptime(time_str, '%Y-%m-%d %H:%M:%S.%f')
        except ValueError:
            try:
                # Try parsing without microseconds
                return datetime.strptime(time_str, '%Y-%m-%d %H:%M:%S')
            except ValueError:
                # Return current time if parsing fails
                self.logger.error(f"Failed to parse time string: {time_str}")
                return datetime.now()

    def convert_to_points(self, profit, symbol):
        """Enhanced conversion of profit to points with proper null handling."""
        try:
            if profit is None or self.point.get(symbol) is None:
                return 0.0
            
            # Get lot size from position if available, otherwise use default
            lot_size = getattr(self, 'lot_size', 0.1)  # Default to 0.1 if not set
            point_value = self.point[symbol] * lot_size * 10000
            
            # Avoid division by zero
            if point_value == 0:
                return 0.0
            
            return profit / point_value
        except Exception as e:
            self.logger.debug(f"Error converting profit to points: {str(e)}")
            return 0.0

    def update_trade_history_on_close(self, ticket, symbol, profit_points, reason):
        """Enhanced trade history update with better error handling"""
        try:
            with self.command_lock:
                close_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f')
                
                # Safely calculate actual profit
                try:
                    point_value = self.point.get(symbol, 0.0)
                    lot_size = getattr(self, 'lot_size', 0.1)
                    actual_profit = profit_points * point_value * lot_size * 10000 if all(v is not None for v in [profit_points, point_value, lot_size]) else 0.0
                except Exception as e:
                    self.logger.debug(f"Error calculating actual profit: {str(e)}")
                    actual_profit = 0.0
                
                # Update profit and close time in all history lists
                for history in [self.trade_history, self.grid_history, self.suretrend_history, self.momentum_history]:
                    if symbol in history:
                        for trade in history[symbol]:
                            try:
                                if trade.get('ticket') == ticket:
                                    trade['profit'] = actual_profit
                                    trade['profit_points'] = profit_points
                                    trade['close_time'] = close_time
                                    trade['close_reason'] = reason
                                    trade['status'] = 'closed'
                                    break
                            except Exception as e:
                                self.logger.debug(f"Error updating trade {ticket}: {str(e)}")
                            continue
                
                self.save_trade_history()
                
        except Exception as e:
            self.logger.error(f"Error updating trade history on close: {str(e)}")

    def get_rates(self, symbol, num_candles=100, timeframe=None):
        """Enhanced rate retrieval with better error handling"""
        if self.simulate:
            return self.get_simulated_rates(symbol, num_candles, timeframe)
        
        retry_count = 0
        while retry_count < self.max_retries:
            try:
                # First ensure MT5 is initialized
                if not self.ensure_mt5_connection():
                    raise Exception("Failed to ensure MT5 connection")
                
                # Convert string timeframe to MT5 timeframe constant if needed
                if isinstance(timeframe, str):
                    timeframe = self.timeframe_configs.get(timeframe.upper())
                    if timeframe is None:
                        raise Exception(f"Invalid timeframe string: {timeframe}")
                
                # Verify timeframe is valid
                valid_timeframes = [mt5.TIMEFRAME_M1, mt5.TIMEFRAME_M5, mt5.TIMEFRAME_M15, 
                                  mt5.TIMEFRAME_M30, mt5.TIMEFRAME_H1, mt5.TIMEFRAME_H4]
                if timeframe not in valid_timeframes:
                    raise Exception(f"Invalid timeframe value: {timeframe}")
                
                # Get rates with explicit error checking
                rates = mt5.copy_rates_from_pos(symbol, timeframe, 0, max(num_candles, 100))  # Always get at least 100 candles
                if rates is None:
                    error = mt5.last_error()
                    raise Exception(f"copy_rates_from_pos failed: {error}")
                
                if len(rates) == 0:
                    raise Exception("No rates returned")
                
                # Convert to DataFrame
                df = pd.DataFrame(rates)
                df['time'] = pd.to_datetime(df['time'], unit='s')
                
                # Cache the data
                if symbol in self.data_cache and timeframe in self.data_cache[symbol]:
                    self.data_cache[symbol][timeframe]['df'] = df
                    self.data_cache[symbol][timeframe]['last_time'] = df['time'].iloc[-1]
                
                self.logger.debug(f"[{symbol}] Successfully retrieved {len(df)} candles for {self.get_timeframe_name(timeframe)}")
                return df
                
            except Exception as e:
                retry_count += 1
                self.logger.error(f"[{symbol}] Failed to get rates (attempt {retry_count}/{self.max_retries}): {str(e)}")
                
                if retry_count < self.max_retries:
                    sleep_time = min(300, self.retry_delay * (2 ** (retry_count - 1)) + random.uniform(0, 1))
                    self.logger.info(f"[{symbol}] Waiting {sleep_time:.1f} seconds before retry...")
                    time.sleep(sleep_time)
                    
                    # Try to use cached data if available
                    if symbol in self.data_cache and timeframe in self.data_cache[symbol]:
                        cached_df = self.data_cache[symbol][timeframe]['df']
                        if cached_df is not None and len(cached_df) > 0:
                            self.logger.warning(f"[{symbol}] Using cached data due to rate retrieval failure")
                            return cached_df
                else:
                    self.logger.error(f"[{symbol}] Failed to get rates after {self.max_retries} attempts")
                    # Try one last time to use cached data
                    if symbol in self.data_cache and timeframe in self.data_cache[symbol]:
                        cached_df = self.data_cache[symbol][timeframe]['df']
                        if cached_df is not None and len(cached_df) > 0:
                            self.logger.warning(f"[{symbol}] Using cached data as final fallback")
                            return cached_df
        
        return None

    def monitor_suretrend_conditions(self):
        """Background thread to monitor SureTrend conditions for all symbols and timeframes."""
        while not self.stop_monitoring.is_set():
            try:
                for symbol in self.symbols:
                    for timeframe in self.timeframes:
                        # Get latest data
                        df = self.get_or_update_rates(symbol, timeframe)
                        if df is None or len(df) < 50:
                            continue
                            
                        # Calculate indicators
                        df = self.calculate_indicators(df, timeframe, symbol)
                        
                        # Check MA crossover for invalidation
                        ma_cross = self.check_ma_crossover(df)
                        current_price = df['close'].iloc[-1]
                        
                        # Get tracking data for this symbol/timeframe
                        tracking = self.suretrend_tracking[symbol][timeframe]
                        
                        # Check SureTrend conditions
                        signal_type, _, conditions = self.check_suretrend_signal(df, timeframe, symbol)
                        
                        # Update conditions tracking
                        if conditions:
                            tracking['conditions'].update(conditions)
                        
                        # Check if conditions are met
                        all_conditions_met = all(tracking['conditions'].values())
                        
                        # Handle condition state changes
                        if all_conditions_met and not tracking['conditions_met']:
                            # New signal detected
                            tracking['conditions_met'] = True
                            tracking['signal_type'] = signal_type
                            tracking['start_time'] = df.index[-1]
                            tracking['start_price'] = current_price
                            tracking['ma_invalidated'] = False
                        
                        # Update existing signal
                        if tracking['conditions_met']:
                            # Check for MA crossover invalidation
                            if (tracking['signal_type'] == 'buy' and ma_cross == 'sell') or \
                               (tracking['signal_type'] == 'sell' and ma_cross == 'buy'):
                                tracking['ma_invalidated'] = True
                                tracking['conditions_met'] = False
                            else:
                                # Update duration and deviation
                                if tracking['start_time']:
                                    tracking['duration'] = (df.index[-1] - tracking['start_time']).total_seconds()
                                    if tracking['start_price']:
                                        deviation = current_price - tracking['start_price']
                                        if tracking['signal_type'] == 'sell':
                                            deviation = -deviation
                                        tracking['current_deviation'] = deviation
                
                # Sleep for a short interval
                time.sleep(1)
                
            except Exception as e:
                self.logger.error(f"Error in SureTrend monitoring: {str(e)}")
                time.sleep(5)

    def start_suretrend_monitoring(self):
        """Start the background monitoring thread."""
        if self.monitoring_thread is None or not self.monitoring_thread.is_alive():
            self.stop_monitoring.clear()
            self.monitoring_thread = threading.Thread(target=self.monitor_suretrend_conditions)
            self.monitoring_thread.daemon = True
            self.monitoring_thread.start()
            return "SureTrend monitoring started"

    def stop_suretrend_monitoring(self):
        """Stop the background monitoring thread."""
        if self.monitoring_thread and self.monitoring_thread.is_alive():
            self.stop_monitoring.set()
            self.monitoring_thread.join()
            return "SureTrend monitoring stopped"

    def display_suretrend_checklist(self, symbol=None, timeframe=None):
        """Display the SureTrend conditions checklist."""
        symbols_to_check = [symbol] if symbol else self.symbols
        timeframes_to_check = [timeframe] if timeframe else self.timeframes
        
        output = []
        
        for sym in symbols_to_check:
            for tf in timeframes_to_check:
                tracking = self.suretrend_tracking[sym][tf]
                tf_name = self.get_timeframe_name(tf)
                
                output.append(f"\n=== SureTrend Checklist for {sym} {tf_name} ===")
                
                for cond_name, is_met in tracking['conditions'].items():
                    check = "✓" if is_met else "✗"
                    output.append(f"{check} {cond_name.replace('_', ' ').title()}")
                
                if tracking['conditions_met']:
                    signal_type = tracking['signal_type'].upper() if tracking['signal_type'] else 'UNKNOWN'
                    duration = timedelta(seconds=int(tracking['duration'])) if tracking['duration'] else timedelta()
                    deviation = tracking['current_deviation']
                    
                    output.append(f"\nSignal Type: {signal_type}")
                    output.append(f"Start Time: {tracking['start_time']}")
                    output.append(f"Duration: {duration}")
                    output.append(f"Price Deviation: {deviation:.5f}")
                    
                    if tracking['ma_invalidated']:
                        output.append("⚠️ WARNING: Signal invalidated by MA crossover!")
                
                output.append("")
        
        return "\n".join(output)

    def save_lock_state(self):
        """Save trading lock state to file."""
        try:
            lock_data = {
                'locked': self.trading_locked,
                'reason': self.trading_lock_reason,
                'date': datetime.now().strftime('%Y-%m-%d')
            }
            with open(self.lock_file, 'w') as f:
                json.dump(lock_data, f)
        except Exception as e:
            self.logger.error(f"Error saving lock state: {str(e)}")

    def __init__(self, mt5_login=None, mt5_password=None, mt5_server=None, symbols=None, timeframes=None, lot_size=0.1, daily_max_profit=500, simulate=False, risk_percent=2.0, mt5_path=None):
        # Initialize trading lock state before other attributes
        self.trading_locked = False
        self.lock_reason = None
        
        # Add SureTrend tracking attributes
        self.suretrend_tracking = {
            symbol: {
                tf: {
                    'conditions_met': False,
                    'signal_type': None,  # 'buy' or 'sell'
                    'start_time': None,
                    'start_price': None,
                    'current_deviation': 0,
                    'ma_invalidated': False,
                    'duration': 0,
                    'conditions': {
                        'trend_aligned': False,
                        'momentum_confirmed': False,
                        'volatility_suitable': False,
                        'ma_alignment': False
                    }
                } for tf in (timeframes or [])
            } for symbol in (symbols or [])
        }
        
        # Create monitoring control attributes
        self.stop_monitoring = threading.Event()
        self.monitoring_thread = None
        
        # Continue with existing initialization
        self.mt5_login = mt5_login
        self.mt5_password = mt5_password
        self.mt5_server = mt5_server
        self.symbols = symbols or []
        self.timeframes = timeframes or []
        self.lot_size = lot_size
        self.daily_max_profit = daily_max_profit
        self.simulate = simulate
        self.risk_percent = risk_percent
        self.mt5_path = mt5_path
        
        self.mt5_connected = False
        self.mt5_account_info = None
        self.mt5_account_balance = 0
        self.mt5_account_equity = 0
        self.mt5_account_margin = 0
        self.mt5_account_free_margin = 0
        self.mt5_account_margin_level = 0
        self.mt5_account_margin_free = 0
        self.mt5_account_margin_level = 0
        self.mt5_account_margin_so = 0
        self.mt5_account_margin_so_call = 0
        self.mt5_account_margin_so_mode = 0
        self.mt5_account_margin_so_mode_text = ""
        self.mt5_account_margin_so_mode_color = ""
        self.mt5_account_margin_so_mode_text_color = ""
        self.mt5_account_margin_so_mode_bg_color = ""
        self.mt5_account_margin_so_mode_border_color = ""
        self.mt5_account_margin_so_mode_border_width = 0
        self.mt5_account_margin_so_mode_border_style = ""
        self.mt5_account_margin_so_mode_border_radius = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
#python start3.py --mt5-login 61339636 --mt5-password "Neema@#54" --mt5-server "Pepperstone-Demo" --symbols XAUUSD EURUSD US500 NAS100 USDJPY --timeframes M1 M5 M15 M30 H1 H4  --lot-size 0.2 --daily-max-profit 1000  --risk-percent 1.5
#python start3.py --mt5-login 61339636 --mt5-password "Neema@#54" --mt5-server "Pepperstone-Demo" --symbols XAUUSD --timeframes M1 M5 --lot-size 0.2 --daily-max-profit 1000  --risk-percent 1.5
import os
import sys
import time
import shutil
import json
import queue
import random
import logging
import warnings
import threading
import argparse
import subprocess
import MetaTrader5 as mt5
from datetime import datetime, timedelta
import pandas as pd
import numpy as np
import plotly.graph_objects as go
import re
import requests
import keyboard
import colorlog
import talib
import psutil
import atexit
from reportlab.lib import colors
from reportlab.lib.pagesizes import letter
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Image, Table, TableStyle
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from prompt_toolkit import PromptSession
from prompt_toolkit.completion import WordCompleter
from prompt_toolkit.history import InMemoryHistory
from concurrent.futures import ThreadPoolExecutor
import tempfile
import shutil
from tqdm import tqdm

warnings.filterwarnings("ignore", category=UserWarning, message="Pandas doesn't allow columns to be created via a new attribute name")

class TradingStrategy:
    def __init__(self, mt5_login=None, mt5_password=None, mt5_server=None, symbols=None, timeframes=None, lot_size=0.1, daily_max_profit=500, simulate=False, risk_percent=2.0, mt5_path=None):
        # Initialize trading lock state before other attributes
        self.trading_locked = False
        self.trading_lock_reason = ""
        # Setup logging first       
        self._setup_logging()
        self.simulate = False
        # Add drawdown tracking attributes
        self.balance_file = "daily_balance.json"
        self.max_drawdown_percent = 50  # 50% maximum drawdown
        self.initial_balance = None
        self.lowest_balance = None
        self.load_daily_balance()
        self.initialize_daily_balance()
        self.mt5_login = mt5_login or 61318849
        self.mt5_password = mt5_password or "Neema@#54"
        self.mt5_server = mt5_server or "Pepperstone-Demo"
            # Initialize status update thread
        self.status_update_interval = 1  # Update every second
        self.status_thread_running = True
        self.status_thread = threading.Thread(target=self.status_update_loop, daemon=True)
        self.status_thread.start()
        
        # Initialize mock trade manager
        self.mock_trade_manager = MockTradeManager(self)

        # Add market check intervals
        self.market_check_interval = 60  # Check market status every 60 seconds
        self.market_closed_sleep = 300   # Sleep for 5 minutes when market is closed

        self.ADMIN_PASSWORD = "TR@d3L3@d3r2025#"  # Complex password for admin override
        self.max_daily_loss = -500  # Set maximum daily loss in points (negative value)
        # Add lock file path
        self.lock_file = "trading_lock.json"
        # Load lock state from file
        self.load_lock_state()

        # Add report generation folder
        self.reports_folder = "trade_reports"
        os.makedirs(self.reports_folder, exist_ok=True)
        
        # Register Times New Roman font
        pdfmetrics.registerFont(TTFont('Times-Roman', 'times.ttf'))
        self.accounts = {
            'default': {'login': self.mt5_login, 'password': self.mt5_password, 'server': self.mt5_server}
        }
        self.current_account = 'default'
        self.sync_enabled = False

        self.TELEGRAM_BOT_TOKEN = "7135089206:AAEmnAztKDkjXg5jM4dXbrjfF3dCvcwJ9Ow"
        self.TELEGRAM_CHAT_ID = "6178394807"
        self.telegram_offset = 0

        self.symbols = symbols if symbols is not None else ['XAUUSD']

        # Initialize symbol_info dictionary
        self.symbol_info = {symbol: {} for symbol in self.symbols}
        self.point = {symbol: None for symbol in self.symbols}

        # Define timeframe_configs before using it in parse_timeframe
        self.timeframe_configs = {
            'M1': mt5.TIMEFRAME_M1, 'M5': mt5.TIMEFRAME_M5, 'M15': mt5.TIMEFRAME_M15,
            'M30': mt5.TIMEFRAME_M30, 'H1': mt5.TIMEFRAME_H1, 'H4': mt5.TIMEFRAME_H4
        }
        # Now parse timeframes after timeframe_configs is defined
        self.timeframes = [self.parse_timeframe(tf) for tf in (timeframes or ['M1'])]

        self.timeframe_intervals = {
            mt5.TIMEFRAME_M1: 60, mt5.TIMEFRAME_M5: 300, mt5.TIMEFRAME_M15: 900,
            mt5.TIMEFRAME_M30: 1800, mt5.TIMEFRAME_H1: 3600, mt5.TIMEFRAME_H4: 14400
        }

        self.lot_size = lot_size
        self.deviation = 10

        self.lot_size = lot_size
        self.deviation = 10  # Adjusted to match second half
        self.max_retries = 3
        self.retry_delay = 5
        self.simulate = simulate
        self.risk_percent = risk_percent
        self.daily_max_profit = daily_max_profit

        self.primary_strategy_enabled = True
        self.suretrend_automation_enabled = False
        self.grid_trading_enabled = False
        self.grid_automation_enabled = False
        self.momentum_automation_enabled = False  # Removed momentum_enabled, using automation flag only

        self.grid_levels = 5
        self.grid_spacing = 10

        self.ma_configs = {
            tf: {'fast': 3 if tf in [mt5.TIMEFRAME_M1, mt5.TIMEFRAME_M5] else 5,
                 'slow': 8 if tf in [mt5.TIMEFRAME_M1, mt5.TIMEFRAME_M5] else 10,
                 'exit_fast': 5, 'exit_slow': 10}
            for tf in self.timeframes  # Changed to self.timeframes for consistency
        }
        self.macd_fast, self.macd_slow, self.macd_signal = 12, 26, 9
        self.momentum_period = 14
        self.psar_step, self.psar_max = 0.02, 0.2
        self.bollinger_period, self.bollinger_dev = 20, 2
        self.atr_period = 14

        self.breakeven_configs = {tf: 50.0 for tf in self.timeframes}
        self.trailing_stop_configs = {tf: 50.0 for tf in self.timeframes}
        self.trailing_delay_configs = {tf: 50.0 for tf in self.timeframes}
        self.signal_cooldown = 300  # 5 minutes default, matching second half
        self.initial_sl = 200  # Default SL in points, matching second half
        #self.initial_balance = 1000
        self.dynamic_management_enabled = False  # Aligned with second half default
        self.exit_signals_enabled = True
        self.use_m5_exit = False

        self.positions = {symbol: {} for symbol in self.symbols}
        self.daily_profit = {symbol: 0.0 for symbol in self.symbols}
        self.daily_trades = {symbol: [] for symbol in self.symbols}  # Simplified to list per symbol
        self.trade_history = {symbol: [] for symbol in self.symbols}
        self.grid_history = {symbol: [] for symbol in self.symbols}
        self.suretrend_history = {symbol: [] for symbol in self.symbols}
        self.momentum_history = {symbol: [] for symbol in self.symbols}
        self.trading_allowed = {symbol: True for symbol in self.symbols}
        self.last_check_times = {symbol: {tf: datetime.now() for tf in self.timeframes} for symbol in self.symbols}
        self.last_signal_times = {symbol: {tf: datetime.now() - timedelta(seconds=self.signal_cooldown) for tf in self.timeframes} for symbol in self.symbols}
        self.waiting_for_trade_confirmation = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.trade_confirmation_queue = queue.Queue()
        self.command_lock = threading.Lock()
        self.context_symbol = None
        self.threads = []
        self.symbol_terminal_threads = {}

        # Initialize ma_exit_enabled with both string and numeric timeframe keys
        self.ma_exit_enabled = {}
        for symbol in self.symbols:
            self.ma_exit_enabled[symbol] = {}
            for tf in self.timeframes:
                # Add numeric timeframe key
                self.ma_exit_enabled[symbol][tf] = False
                # Add string timeframe key
                tf_name = self.get_timeframe_name(tf)
                self.ma_exit_enabled[symbol][tf_name] = False
                # Special case for M5
                if tf_name == 'M5':
                    self.ma_exit_enabled[symbol][tf_name] = self.use_m5_exit

        self.volatility_check_enabled = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.psar_filter_enabled = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.psar_filter_timeframe = {symbol: {tf: mt5.TIMEFRAME_H1 for tf in self.timeframes} for symbol in self.symbols}
        self.data_cache = {symbol: {tf: {'df': None, 'last_time': None} for tf in self.timeframes} for symbol in self.symbols}
        self.suretrend_conditions_met = {symbol: {tf: {'buy': False, 'sell': False} for tf in self.timeframes} for symbol in self.symbols}
        self.trades_per_strategy = {symbol: {tf: {"primary": 0, "suretrend": 0, "grid": 0, "momentum": 0, "breakout_momentum": 0} for tf in self.timeframes} for symbol in self.symbols}

        self._setup_logging()
        self.load_trade_history()
        atexit.register(self.cleanup)
        keyboard.on_press_key("q", self.handle_exit)

        # Enhanced error handling settings
        self.max_consecutive_errors = 3
        self.error_cooldown = 60  # seconds
        self.last_error_time = None
        self.consecutive_errors = 0
        
        # Load saved Telegram offset
        self.load_telegram_offset()
        
        # Initialize connection status
        self.mt5_connected = False
        self.telegram_connected = False

        # Add semi-automated mode variables
        self.primary_strategy_semi_auto = False
        self.suretrend_semi_auto = False
        self.grid_semi_auto = False
        self.momentum_semi_auto = False

        # Add MT5 path to the initialization
        self.mt5_path = mt5_path or r"C:\Program Files\MetaTrader 5\terminal64.exe"

        # Add new sync-related attributes
        self.sync_interval = 1  # Sync every 1 second
        self.last_sync_time = datetime.now()
        self.last_known_positions = {symbol: {} for symbol in self.symbols}
        self.last_known_history = {symbol: set() for symbol in self.symbols}
        self.external_trade_defaults = {
            'sl_points': 200,  # Default SL in points
            'tp_ratio': 2.0,   # TP = SL * tp_ratio
            'timeframe': mt5.TIMEFRAME_M1  # Default timeframe for external trades
        }
        
        # Start continuous sync thread
        self.sync_thread = threading.Thread(target=self.continuous_sync_loop, daemon=True)
        self.sync_thread.start()

        # Add HFScalper strategy attributes
        self.hfscalper_enabled = False
        self.hfscalper_semi_auto = False
        self.hfscalper_min_momentum = 0.0001
        self.hfscalper_volatility_threshold = 1.5
        self.hfscalper_tp_points = 10
        self.hfscalper_psar_enabled = False
        self.hfscalper_psar_step = 0.02
        self.hfscalper_psar_max = 0.2
        self.hfscalper_history = {symbol: [] for symbol in (symbols or ['XAUUSD'])}

        self.breakout_momentum_enabled = False
        self.breakout_momentum_semi_auto = False
        self.breakout_momentum_history = {symbol: [] for symbol in self.symbols}
        self.rsi_period = 14  # RSI period for overbought/oversold detection
        self.rsi_overbought = 70
        self.rsi_oversold = 30
        self.consolidation_lookback = 20  # Lookback period for consolidation detection
        self.consolidation_threshold = 0.05  # BB width threshold for consolidation
        self.breakout_multiplier = 1.5  # TP multiplier based on consolidation range
        self.atr_multiplier_sl = 1.5  # SL multiplier based on ATR
        self.atr_multiplier_trailing = 1.0  # Trailing stop multiplier

        # Add new signal optimization attributes
        self.signal_optimization_enabled = False
        self.realtime_signals_enabled = True
        self.signal_quality_threshold = 0.7
        self.signal_interval = 1  # seconds
        self.signal_history = {symbol: {tf: [] for tf in self.timeframes} for symbol in self.symbols}
        self.signal_performance = {symbol: {tf: {'total': 0, 'successful': 0} for tf in self.timeframes} for symbol in self.symbols}
        self.signal_alerts_enabled = True
        self.signal_logging_enabled = True
        self.signal_filters = {
            'momentum_threshold': 0.0001,
            'volatility_threshold': 1.5,
            'min_confirmation_signals': 2,
            'min_signal_quality': 0.7
        }
        
        self.strategy_performance = {
            'primary': {'total': 0, 'successful': 0, 'profit': 0.0},
            'suretrend': {'total': 0, 'successful': 0, 'profit': 0.0},
            'grid': {'total': 0, 'successful': 0, 'profit': 0.0},
            'momentum': {'total': 0, 'successful': 0, 'profit': 0.0},
            'hfscalper': {'total': 0, 'successful': 0, 'profit': 0.0},
            'breakout_momentum': {'total': 0, 'successful': 0, 'profit': 0.0}
        }
        
        # Signal quality metrics
        self.signal_quality_metrics = {
            'accuracy': 0.0,
            'profit_factor': 0.0,
            'win_rate': 0.0,
            'avg_profit': 0.0,
            'avg_loss': 0.0
        }

        # Add SureTrend tracking attributes
        self.suretrend_tracking = {
            symbol: {
                tf: {
                    'conditions_met': False,
                    'signal_type': None,  # 'buy' or 'sell'
                    'start_time': None,
                    'start_price': None,
                    'current_deviation': 0,
                    'ma_invalidated': False,
                    'duration': 0,
                    'conditions': {
                        'trend_aligned': False,
                        'momentum_confirmed': False,
                        'volatility_suitable': False,
                        'ma_alignment': False
                    }
                } for tf in (timeframes or [])
            } for symbol in (symbols or [])
        }
        
        # Create an event to signal monitoring thread to stop
        self.stop_monitoring = threading.Event()
        
        # Create a thread for background monitoring
        self.monitoring_thread = None

    def _setup_logging(self):
        log_folder = "live_trading_logs"
        os.makedirs(log_folder, exist_ok=True)
        log_file = os.path.join(log_folder, f"trading_log_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log")
        
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)
        
        # Custom formatter using TerminalManager colors
        class ColoredFormatter(logging.Formatter):
            def format(self, record):
                if record.levelno >= logging.ERROR:
                    color = self.terminal.COLORS['red']
                elif record.levelno >= logging.WARNING:
                    color = self.terminal.COLORS['yellow']
                elif record.levelno >= logging.INFO:
                    color = self.terminal.COLORS['green']
                else:
                    color = self.terminal.COLORS['blue']
                
                record.msg = f"{color}{record.msg}{self.terminal.COLORS['reset']}"
                return super().format(record)
        
        # Set up handlers with the new formatter
        formatter = ColoredFormatter('%(asctime)s | %(levelname)s | %(message)s')
        
        # Console handler
        ch = logging.StreamHandler()
        ch.setFormatter(formatter)
        self.logger.addHandler(ch)
        
        # File handler
        fh = logging.FileHandler(log_file)
        fh.setFormatter(logging.Formatter('%(asctime)s | %(levelname)s | %(message)s'))
        self.logger.addHandler(fh)

    def update_status_line(self):
        """Update the status line with current system state."""
        try:
            # Get connection status
            mt5_status = "Connected" if self.mt5_connected else "Disconnected"
            telegram_status = "Connected" if self.telegram_connected else "Disconnected"
            
            # Get trade counts
            active_trades = sum(len(self.positions[s]) for s in self.symbols)
            mock_trades = len(self.mock_trade_manager.mock_trades)
            
            # Get profit
            daily_profit = sum(self.convert_to_points(self.daily_profit[s], s) for s in self.symbols)
            
            status = (
                f"Last Update: {datetime.now().strftime('%H:%M:%S')} | "
                f"MT5: {mt5_status} | Telegram: {telegram_status} | "
                f"Active Trades: {active_trades} | Mock Trades: {mock_trades} | "
                f"Daily Profit: {daily_profit:.1f} pts"
            )
            
            self.terminal.update_status(status)
        except Exception as e:
            self.logger.error(f"Error updating status line: {str(e)}")

    def parse_timeframe(self, tf_str):
        tf_str = tf_str.upper()
        return self.timeframe_configs.get(tf_str)

    def get_timeframe_name(self, timeframe):
        for name, value in self.timeframe_configs.items():
            if value == timeframe:
                return name
        return "Unknown"

    def get_telegram_updates(self):
        """Enhanced Telegram updates with proper offset handling and better timeout handling."""
        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/getUpdates"
        
        retry_count = 0
        while retry_count < self.max_retries:
            try:
                params = {
                    "offset": self.telegram_offset,
                    "timeout": 30,
                    "allowed_updates": ["message"]
                }
                
                # Increase timeout and add backoff strategy
                response = requests.get(url, params=params, timeout=60)
                response.raise_for_status()
                
                updates = response.json()
                if updates.get("ok") and "result" in updates:
                    if updates["result"]:
                        latest_update = max(update["update_id"] for update in updates["result"])
                        self.telegram_offset = latest_update + 1
                        self.save_telegram_offset()
                    return updates
                    
                time.sleep(1)
                
            except requests.exceptions.Timeout:
                retry_count += 1
                self.logger.warning(f"Telegram timeout (attempt {retry_count}/{self.max_retries}), retrying...")
                time.sleep(5 * retry_count)  # Progressive backoff
            except requests.exceptions.RequestException as e:
                retry_count += 1
                self.logger.error(f"Failed to get Telegram updates (attempt {retry_count}/{self.max_retries}): {str(e)}")
                if retry_count == self.max_retries:
                    time.sleep(60)
                    retry_count = 0
                else:
                    time.sleep(5 * retry_count)
        
        return None

    def save_telegram_offset(self):
        """Save Telegram offset to file."""
        try:
            with open("telegram_offset.txt", "w") as f:
                f.write(str(self.telegram_offset))
        except Exception as e:
            self.logger.error(f"Failed to save Telegram offset: {e}")

    def load_telegram_offset(self):
        """Load Telegram offset from file."""
        try:
            if os.path.exists("telegram_offset.txt"):
                with open("telegram_offset.txt", "r") as f:
                    self.telegram_offset = int(f.read().strip())
        except Exception as e:
            self.logger.error(f"Failed to load Telegram offset: {e}")

    def send_telegram_message(self, message, thread_id=None, chart_path=None, chat_id=None):
        """Enhanced Telegram message sending with better timeout handling"""
        if not self.TELEGRAM_BOT_TOKEN or not self.TELEGRAM_CHAT_ID:
            self.logger.warning("Telegram credentials not configured")
            return None

        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendMessage"
        max_length = 4096
        chat_id = chat_id or self.TELEGRAM_CHAT_ID
        
        # Format message
        formatted_message = f"> GC_Signals:\n{message}"
        formatted_message = formatted_message.replace('<', '&lt;').replace('>', '&gt;')
        
        # Split long messages
        if len(formatted_message) > max_length:
            parts = []
            current_part = "> GC_Signals:\n"
            for line in message.split('\n'):
                if len(current_part) + len(line) + 1 <= max_length:
                    current_part += line + '\n'
                else:
                    parts.append(current_part.strip())
                    current_part = f"> GC_Signals:\n{line}\n"
            if current_part:
                parts.append(current_part.strip())
        else:
            parts = [formatted_message]
        
        last_message_id = None
        for part in parts:
            retry_count = 0
            while retry_count < self.max_retries:
                try:
                    payload = {
                        "chat_id": chat_id,
                        "text": part,
                        "parse_mode": "HTML"
                    }
                    
                    if thread_id and not last_message_id:
                        payload["reply_to_message_id"] = thread_id
                    elif last_message_id:
                        payload["reply_to_message_id"] = last_message_id

                    response = requests.post(url, json=payload, timeout=30)  # Increased timeout
                    response.raise_for_status()
                    
                    result = response.json()
                    if not result.get("ok"):
                        raise Exception(f"Telegram API error: {result.get('description')}")
                        
                    last_message_id = result.get("result", {}).get("message_id")
                    
                    # Send chart if available
                    if chart_path and last_message_id and part == parts[-1]:
                        try:
                            with open(chart_path, 'rb') as chart_file:
                                files = {'photo': chart_file}
                                photo_url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendPhoto"
                                photo_response = requests.post(
                                    photo_url,
                                    data={"chat_id": chat_id, "reply_to_message_id": last_message_id},
                                    files=files,
                                    timeout=30  # Increased timeout
                                )
                                photo_response.raise_for_status()
                        except Exception as e:
                            self.logger.error(f"Failed to send chart: {e}")
                    
                    break
                    
                except Exception as e:
                    retry_count += 1
                    self.logger.error(f"Failed to send Telegram message (attempt {retry_count}/{self.max_retries}): {e}")
                    if retry_count == self.max_retries:
                        return None
                    time.sleep(5 * retry_count)  # Progressive backoff
        
        return last_message_id

    def load_trade_history(self):
        for symbol in self.symbols:
            for filename, history_dict in [
                (f"trade_history_{symbol}.json", self.trade_history),
                (f"grid_history_{symbol}.json", self.grid_history),
                (f"suretrend_history_{symbol}.json", self.suretrend_history),
                (f"momentum_history_{symbol}.json", self.momentum_history)
            ]:
                if os.path.exists(filename):
                    with open(filename, 'r') as f:
                        try:
                            history_dict[symbol] = json.load(f)
                            self.logger.info(f"[{symbol}] Loaded {len(history_dict[symbol])} trades from {filename}")
                        except json.JSONDecodeError:
                            self.logger.error(f"[{symbol}] Failed to load {filename}")

    def save_trade_history(self):
        for symbol in self.symbols:
            for filename, history_dict in [
                (f"trade_history_{symbol}.json", self.trade_history),
                (f"grid_history_{symbol}.json", self.grid_history),
                (f"suretrend_history_{symbol}.json", self.suretrend_history),
                (f"momentum_history_{symbol}.json", self.momentum_history)
            ]:
                with open(filename, 'w') as f:
                    json.dump(history_dict[symbol], f, default=str)

    def cleanup(self):
        self.logger.info("Cleaning up...")
        try:
            # Stop status thread
            self.status_thread_running = False
            if hasattr(self, 'status_thread'):
                self.status_thread.join(timeout=2)
            
            # Existing cleanup code...
            with self.command_lock:
                for symbol in self.symbols:
                    for position in list(self.positions[symbol].values()):
                        self.close_position(position, "System shutdown")
                self.save_trade_history()
                
            # Ensure proper MT5 shutdown
            if mt5.terminal_info():
                mt5.shutdown()
                
            # Additional cleanup for background terminal
            try:
                subprocess.run(['taskkill', '/F', '/IM', 'terminal64.exe'], capture_output=True)
            except Exception as e:
                self.logger.warning(f"Failed to force close MT5 terminal: {e}")
        except Exception as e:
            self.logger.error(f"Error during cleanup: {e}")

    def handle_exit(self, e):
        if e.name == 'q':
            self.cleanup()
            os._exit(0)

    def ensure_mt5_connection(self):
        """Enhanced MT5 connection handling with better retry logic"""
        if self.simulate:
            return True

        try:
            # First check if we're already connected
            if mt5.terminal_info() and mt5.account_info():
                return True

            # If not connected, try to initialize
            if not mt5.initialize():
                # Kill any existing MT5 processes first
                try:
                    import subprocess
                    import psutil
                    for proc in psutil.process_iter(['pid', 'name']):
                        try:
                            if proc.info['name'].lower() in ['terminal64.exe', 'metatrader.exe', 'metaeditor64.exe']:
                                subprocess.run(['taskkill', '/F', '/PID', str(proc.info['pid'])], capture_output=True)
                        except (psutil.NoSuchProcess, psutil.AccessDenied):
                            continue
                    time.sleep(2)  # Give time for processes to terminate
                except Exception as e:
                    self.logger.warning(f"Failed to kill existing MT5 processes: {e}")

                # Create a temporary directory for MT5 data
                temp_dir = tempfile.mkdtemp(prefix="mt5_temp_")
                self.logger.info(f"Created temporary directory for MT5: {temp_dir}")

                # Initialize with retries
                for attempt in range(3):
                    try:
                        initialized = mt5.initialize(
                            path=self.mt5_path,
                            login=self.mt5_login,
                            password=self.mt5_password,
                            server=self.mt5_server,
                            portable=True,
                            timeout=60000,
                            config={
                                "show": False,
                                "autoclose": True,
                                "silent": True
                            }
                        )

                        if initialized:
                            # Verify connection
                            if not mt5.account_info():
                                raise Exception("Failed to get account info after initialization")
                            
                            # Initialize symbols
                            for symbol in self.symbols:
                                if not mt5.symbol_select(symbol, True):
                                    raise Exception(f"Failed to select symbol {symbol}")
                                
                                symbol_info = mt5.symbol_info(symbol)
                                if not symbol_info:
                                    raise Exception(f"Failed to get symbol info for {symbol}")
                                
                                self.point[symbol] = symbol_info.point
                                self.symbol_info[symbol] = {
                                    'digits': symbol_info.digits,
                                    'trade_contract_size': symbol_info.trade_contract_size,
                                    'volume_min': symbol_info.volume_min,
                                    'volume_max': symbol_info.volume_max,
                                    'volume_step': symbol_info.volume_step
                                }
                            
                            self.mt5_connected = True
                            return True

                        error = mt5.last_error()
                        if attempt < 2:
                            self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed: {error}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {attempt + 1} attempts: {error}")
                            return False

                    except Exception as e:
                        if attempt < 2:
                            self.logger.warning(f"MT5 initialization error (attempt {attempt + 1}): {str(e)}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {attempt + 1} attempts with error: {str(e)}")
                            return False

            return False

        except Exception as e:
            self.logger.error(f"Error in ensure_mt5_connection: {str(e)}")
            return False

    def initialize_mt5(self):
        """Initialize MT5 connection and point values for all symbols."""
        # Initialize self.point as a dictionary if not already
        if not hasattr(self, 'point') or not isinstance(self.point, dict):
            self.point = {}
    
        if self.simulate:
            # Initialize point values for simulation mode
            for symbol in self.symbols:
                self.point[symbol] = 0.01 if symbol != "XAUUSD" else 0.01
            self.logger.info("Running in simulation mode; MT5 not initialized.")
            return True
    
        try:
            # First, ensure MT5 is completely shut down
            if mt5.terminal_info():
                mt5.shutdown()
            
            # Force kill any existing MT5 processes
            try:
                import subprocess
                import psutil
                
                # Kill terminal64.exe processes
                for proc in psutil.process_iter(['pid', 'name']):
                    try:
                        if proc.info['name'].lower() in ['terminal64.exe', 'metatrader.exe', 'metaeditor64.exe']:
                            subprocess.run(['taskkill', '/F', '/PID', str(proc.info['pid'])], capture_output=True)
                    except (psutil.NoSuchProcess, psutil.AccessDenied):
                        continue
                
                time.sleep(2)  # Give time for processes to terminate
            except Exception as e:
                self.logger.warning(f"Failed to kill existing MT5 processes: {e}")
    
            # Create a temporary directory for MT5 data
            import tempfile
            import shutil
            temp_dir = tempfile.mkdtemp(prefix="mt5_temp_")
            self.logger.info(f"Created temporary directory for MT5: {temp_dir}")
    
            # Initialize MT5 with retries
            max_retries = 3
            for attempt in range(max_retries):
                try:
                    # Initialize with minimal settings first
                    initialized = mt5.initialize(
                        path=self.mt5_path,
                        login=self.mt5_login,
                        password=self.mt5_password,
                        server=self.mt5_server,
                        portable=True,
                        timeout=60000,
                        config={
                            "show": False,
                            "autoclose": True,
                            "silent": True
                        }
                    )
    
                    if not initialized:
                        error = mt5.last_error()
                        if attempt < max_retries - 1:
                            self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed: {error}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {max_retries} attempts: {error}")
                            shutil.rmtree(temp_dir, ignore_errors=True)
                            return False
    
                    # Verify connection and login
                    account_info = mt5.account_info()
                    if not account_info:
                        self.logger.error("Failed to get account info")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
                    # Verify trading is enabled
                    terminal = mt5.terminal_info()
                    if not terminal:
                        self.logger.error("Failed to get terminal info")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
                    if not terminal.trade_allowed:
                        self.logger.warning("AutoTrading is disabled, attempting to enable...")
                        # We'll continue anyway as it might be enabled later
    
                    self.logger.info(f"Successfully connected to account {account_info.login} on {self.mt5_server}")
                    self.logger.info(f"Balance: ${account_info.balance:.2f}, Equity: ${account_info.equity:.2f}")
                    self.logger.info(f"Margin Level: {account_info.margin_level:.2f}%")
                    
                    # Initialize symbols
                    for symbol in self.symbols:
                        if not mt5.symbol_select(symbol, True):
                            self.logger.error(f"Failed to select symbol {symbol}")
                            continue
                        
                        symbol_info = mt5.symbol_info(symbol)
                        if symbol_info:
                            # Store point value in dictionary
                            self.point[symbol] = symbol_info.point
                            self.symbol_info[symbol] = {
                                'digits': symbol_info.digits,
                                'trade_contract_size': symbol_info.trade_contract_size,
                                'volume_min': symbol_info.volume_min,
                                'volume_max': symbol_info.volume_max,
                                'volume_step': symbol_info.volume_step
                            }
                            self.logger.info(f"Initialized {symbol}: Point={symbol_info.point}, "
                                           f"Digits={symbol_info.digits}, "
                                           f"Contract Size={symbol_info.trade_contract_size}")
                        else:
                            self.logger.error(f"Failed to get symbol info for {symbol}")
                            self.point[symbol] = 0.01  # Fallback point value
                            continue  # Try to continue with other symbols
    
                    # Validate that all symbols have point values
                    for symbol in self.symbols:
                        if symbol not in self.point:
                            self.logger.warning(f"No point value set for {symbol}, using fallback value 0.01")
                            self.point[symbol] = 0.01
    
                    self.mt5_connected = True
                    return True
    
                except Exception as e:
                    if attempt < max_retries - 1:
                        self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed with error: {str(e)}. Retrying...")
                        time.sleep(5)
                    else:
                        self.logger.error(f"MT5 initialization failed after {max_retries} attempts with error: {str(e)}")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
        except Exception as e:
            self.logger.error(f"Error in initialize_mt5: {str(e)}")
            return False
        finally:
            # Clean up temporary directory if it exists
            try:
                if 'temp_dir' in locals():
                    shutil.rmtree(temp_dir, ignore_errors=True)
            except Exception as e:
                self.logger.warning(f"Failed to clean up temporary directory: {e}")

    def add_account(self, name, login, password, server):
        if name in self.accounts:
            self.logger.warning(f"Account '{name}' already exists.")
            return False
        self.accounts[name] = {"login": int(login), "password": password, "server": server}
        self.logger.info(f"Added account '{name}' with login {login} and server {server}.")
        # If no current account is set, make this the default and initialize
        if not self.current_account:
            self.current_account = name
            self.mt5_login = login
            self.mt5_password = password
            self.mt5_server = server
            if not self.initialize_mt5():
                self.logger.error(f"Failed to initialize MT5 with new account '{name}'.")
                del self.accounts[name]
                return False
        return True

    def load_daily_balance(self):
        """Load daily balance tracking information from file."""
        try:
            if os.path.exists(self.balance_file):
                with open(self.balance_file, 'r') as f:
                    data = json.load(f)
                    # Check if data is from today
                    saved_date = datetime.strptime(data.get('date', ''), '%Y-%m-%d').date()
                    if saved_date == datetime.now().date():
                        self.initial_balance = data.get('initial_balance')
                        self.lowest_balance = data.get('lowest_balance')
                        self.trading_locked = data.get('trading_locked', False)
                        self.trading_lock_reason = data.get('lock_reason', '')
                    else:
                        # New day, get fresh balance
                        self.initialize_daily_balance()
            else:
                self.initialize_daily_balance()
        except Exception as e:
            self.logger.error(f"Error loading daily balance: {str(e)}")
            self.initialize_daily_balance()


    def initialize_daily_balance(self):
        """Initialize daily balance tracking with current MT5 account balance."""
        try:
            if not self.simulate:
                # First ensure MT5 connection
                if not self.ensure_mt5_connection():
                    self.logger.error("Failed to connect to MT5 for balance initialization")
                    return
    
                # Get actual account balance from MT5
                account_info = mt5.account_info()
                if account_info:
                    self.initial_balance = account_info.balance
                    self.lowest_balance = account_info.balance
                    self.trading_locked = False
                    self.trading_lock_reason = ""
                    self.logger.info(f"Initialized daily balance tracking with MT5 balance: ${self.initial_balance:.2f}")
                else:
                    # Log error and exit if can't get balance
                    self.logger.error("Failed to get MT5 account balance")
                    return
            else:
                # For simulation, get actual balance first
                account_info = mt5.account_info()
                if account_info:
                    self.initial_balance = account_info.balance
                else:
                    self.initial_balance = 146.52  # Use current actual balance as fallback
                self.lowest_balance = self.initial_balance
                self.trading_locked = False
                self.trading_lock_reason = ""
    
            self.save_daily_balance()
    
        except Exception as e:
            self.logger.error(f"Error initializing daily balance: {str(e)}")
            # Do not set any default values, just log error and return
            return

    def save_daily_balance(self):
        """Save daily balance tracking information to file."""
        try:
            data = {
                'date': datetime.now().strftime('%Y-%m-%d'),
                'initial_balance': self.initial_balance,
                'lowest_balance': self.lowest_balance,
                'trading_locked': self.trading_locked,
                'lock_reason': self.trading_lock_reason
            }
            with open(self.balance_file, 'w') as f:
                json.dump(data, f)
        except Exception as e:
            self.logger.error(f"Error saving daily balance: {str(e)}")

    def check_drawdown(self):
        """Check if current drawdown exceeds maximum allowed percentage."""
        try:
            if not self.initial_balance:
                return False

            current_balance = 0
            if not self.simulate:
                # Get fresh balance from MT5
                account_info = mt5.account_info()
                if account_info:
                    current_balance = account_info.balance
                else:
                    self.logger.error("Failed to get current MT5 balance")
                    return False
            else:
                # In simulation mode, calculate from tracked profits
                current_balance = self.initial_balance + sum(self.daily_profit.values())

            # Skip drawdown check if initial balance is zero or null
            if not self.initial_balance:
                return False

            # Update lowest balance if current is lower
            if self.lowest_balance is None or current_balance < self.lowest_balance:
                self.lowest_balance = current_balance
                self.save_daily_balance()

            # Calculate drawdown percentage using actual values
            drawdown_percent = ((self.initial_balance - current_balance) / self.initial_balance) * 100 if self.initial_balance > 0 else 0

            if drawdown_percent >= self.max_drawdown_percent:
                message = (
                    f"⚠️ MAXIMUM DRAWDOWN REACHED ⚠️\n"
                    f"Initial Balance: ${self.initial_balance:.2f}\n"
                    f"Current Balance: ${current_balance:.2f}\n"
                    f"Drawdown: {drawdown_percent:.2f}%\n"
                    f"Trading will be locked for the rest of the day."
                )
                self.lock_trading(message)
                self.save_daily_balance()
                return True

            return False

        except Exception as e:
            self.logger.error(f"Error checking drawdown: {str(e)}")
            return False

    def switch_account(self, name):
        if name not in self.accounts:
            self.logger.error(f"Account '{name}' not found.")
            return False
        if name == self.current_account:
            self.logger.info(f"Already on account '{name}'.")
            return True
        
        # Store current positions before switching
        current_positions = {symbol: dict(self.positions[symbol]) for symbol in self.symbols}
        
        # Update current account details
        self.current_account = name
        self.mt5_login = self.accounts[name]["login"]
        self.mt5_password = self.accounts[name]["password"]
        self.mt5_server = self.accounts[name]["server"]
        
        # Reinitialize MT5 with new account
        if not self.initialize_mt5():
            self.logger.error(f"Failed to switch to account '{name}'.")
            return False
        
        # Restore positions or sync with new account
        self.positions = {symbol: {} for symbol in self.symbols}  # Reset positions
        self.sync_positions_with_mt5()
        
        self.logger.info(f"Switched to account '{name}' successfully.")
        return True

    def sync_positions_with_mt5(self):
        """Enhanced synchronization with MT5 including proper script trade tracking."""
        if self.simulate:
            return True

        try:
            # Get all current MT5 positions
            mt5_positions = mt5.positions_get()
            if mt5_positions is None:
                self.logger.error("Failed to get positions from MT5")
                return False
                
            mt5_tickets = {pos.ticket for pos in mt5_positions}
            
            # Use a timeout context for the lock
            if not self.command_lock.acquire(timeout=5):
                self.logger.error("Failed to acquire lock for position synchronization")
                return False
                
            try:
                for symbol in self.symbols:
                    # Check for positions that exist in our tracking but not in MT5
                    for ticket in list(self.positions[symbol].keys()):
                        if ticket not in mt5_tickets:
                            # Position was closed externally
                            position = self.positions[symbol][ticket]
                            self.logger.info(f"[{symbol}] Position {ticket} closed externally, updating records")
                            
                            # Calculate final profit if possible
                            profit_points = 0
                            if mt5_positions:
                                for mt5_pos in mt5_positions:
                                    if mt5_pos.ticket == ticket:
                                        profit_points = self.convert_to_points(mt5_pos.profit, symbol)
                                        break
                            
                            # Update trade history
                            self.update_trade_history_on_close(ticket, symbol, profit_points, "Closed externally")
                            
                            # Remove from tracking
                            del self.positions[symbol][ticket]
                    
                    # Add any new positions from MT5 that we're not tracking
                    for pos in mt5_positions:
                        if pos.symbol == symbol and pos.ticket not in self.positions[symbol]:
                            # Check if this is a script-placed trade based on comment
                            is_script_trade = pos.comment and pos.comment.startswith("GC_Signals_")
                            strategy = pos.comment.replace("GC_Signals_", "") if is_script_trade else "external"
                            
                            if not is_script_trade:
                                # This is an external trade - add it with external trade handling
                                self.handle_external_trade(pos)
                            else:
                                # This is our trade that somehow got disconnected - restore it
                                self.positions[symbol][pos.ticket] = {
                                    'ticket': pos.ticket,
                                    'type': pos.type,
                                    'entry_price': pos.price_open,
                                    'lot_size': pos.volume,
                                    'sl': pos.sl,
                                    'tp': pos.tp,
                                    'timeframe': mt5.TIMEFRAME_M1,  # Default to M1 if unknown
                                    'strategy': strategy,
                                    'entry_time': datetime.fromtimestamp(pos.time).strftime('%Y-%m-%d %H:%M:%S.%f'),
                                    'signal_time': datetime.fromtimestamp(pos.time).strftime('%Y-%m-%d %H:%M:%S.%f'),
                                    'breakeven_triggered': False,
                                    'trailing_active': False,
                                    'thread_id': None,
                                    'reason': strategy,
                                    'comments': pos.comment,
                                    'symbol': symbol,
                                    'profit': pos.profit,
                                    'script_placed': True
                                }
                                self.logger.info(f"[{symbol}] Restored script-placed trade {pos.ticket}")
            finally:
                self.command_lock.release()
            
            self.save_trade_history()
            return True
            
        except Exception as e:
            self.logger.error(f"Error in sync_positions_with_mt5: {str(e)}")
            if self.command_lock.locked():
                self.command_lock.release()
            return False

    def prompt_position_params(self, position):
        """Prompt for position parameters after trade entry."""
        symbol = position['symbol']
        point = self.point[symbol]  # Get point value directly from self.point dictionary
        
        # Calculate current parameters in points
        current_sl_points = abs(position['sl'] - position['entry_price']) / point if position['sl'] else 0
        current_tp_points = abs(position['tp'] - position['entry_price']) / point if position['tp'] else 0
        
        message = (
            f"🔧 Position Parameters Required:\n"
            f"Ticket: {position['ticket']}\n"
            f"Symbol: {symbol}\n"
            f"Entry: {position['entry_price']:.5f}\n"
            f"Current Settings:\n"
            f"- SL: {current_sl_points:.0f} points\n"
            f"- TP: {current_tp_points:.0f} points\n"
            f"- Trail Stop: {self.trailing_stop_configs[position['timeframe']]:.1f} points\n"
            f"- Trail Delay: {self.trailing_delay_configs[position['timeframe']]:.1f} points\n"
            f"- MA Exit: {'Enabled' if self.ma_exit_enabled[symbol][position['timeframe']] else 'Disabled'}\n\n"
            f"Reply with: setparams <ticket> <sl_points> <tp_points> <trail_stop> <trail_delay> <ma_exit>\n"
            f"Example: setparams {position['ticket']} 100 200 20 50 1\n"
            f"(Use 0 for default values, 1/0 for ma_exit enable/disable)"
        )
        
        # Send to both interfaces
        self.send_telegram_message(message)
        print(f"\n{message}")
        position['waiting_params'] = True

    def handle_position_params(self, cmd_parts):
        """Handle the setparams command for position parameters."""
        try:
            if len(cmd_parts) != 7:
                return "Invalid parameters. Usage: setparams <ticket> <sl_points> <tp_points> <trail_stop> <trail_delay> <ma_exit>"
            
            _, ticket, sl_points, tp_points, trail_stop, trail_delay, ma_exit = cmd_parts
            ticket = int(ticket)
            
            # Find position
            position = None
            symbol = None
            for sym in self.symbols:
                if ticket in self.positions[sym]:
                    position = self.positions[sym][ticket]
                    symbol = sym
                    break
            
            if not position:
                return f"Position with ticket {ticket} not found."
            
            if not position.get('waiting_params', False):
                return f"Position {ticket} is not waiting for parameter settings."
            
            # Get symbol point value
            point = self.point[symbol]
            
            # Calculate actual SL/TP prices based on points
            sl_points = float(sl_points)
            tp_points = float(tp_points)
            
            if sl_points > 0:
                sl = (position['entry_price'] - sl_points * point) if position['type'] == mt5.ORDER_TYPE_BUY else \
                    (position['entry_price'] + sl_points * point)
            else:
                sl = position['sl']
                
            if tp_points > 0:
                tp = (position['entry_price'] + tp_points * point) if position['type'] == mt5.ORDER_TYPE_BUY else \
                    (position['entry_price'] - tp_points * point)
            else:
                tp = position['tp']
            
            trail_stop = float(trail_stop) if float(trail_stop) != 0 else self.trailing_stop_configs[position['timeframe']]
            trail_delay = float(trail_delay) if float(trail_delay) != 0 else self.trailing_delay_configs[position['timeframe']]
            ma_exit = bool(int(ma_exit))
            
            # Apply parameters
            success = self.modify_position(position, sl=sl, tp=tp)
            if not success:
                return "Failed to modify position parameters"
                
            self.trailing_stop_configs[position['timeframe']] = trail_stop
            self.trailing_delay_configs[position['timeframe']] = trail_delay
            self.ma_exit_enabled[symbol][position['timeframe']] = ma_exit
            
            position['waiting_params'] = False
            
            return (f"Parameters set for ticket {ticket}:\n"
                    f"SL: {sl_points:.0f} points (Price: {sl:.5f})\n"
                    f"TP: {tp_points:.0f} points (Price: {tp:.5f})\n"
                    f"Trail Stop: {trail_stop} points\n"
                    f"Trail Delay: {trail_delay} points\n"
                    f"MA Exit: {'Enabled' if ma_exit else 'Disabled'}")
                    
        except Exception as e:
            return f"Error setting parameters: {str(e)}"

    def generate_trade_report(self, ticket=None, symbol=None, daily=False):
        """Generate detailed trade report in PDF format with embedded charts including Parabolic SAR and MACD using TA-Lib."""
        try:
            # Create PDF document
            filename = f"trade_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.pdf"
            filepath = os.path.join(self.reports_folder, filename)
            
            doc = SimpleDocTemplate(filepath, pagesize=letter)
            story = []
            
            # Get trades to report
            trades = []
            title = ""
            if ticket:
                # For ticket-specific report
                title = f"TRADE REPORT TICKET No. {ticket}"
                for sym in self.symbols:
                    # Check current open positions
                    if ticket in self.positions[sym]:
                        position = self.positions[sym][ticket]
                        trade = {
                            'ticket': position['ticket'],
                            'type': "BUY" if position['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                            'entry_price': position['entry_price'],
                            'close_price': None,
                            'sl': position['sl'],
                            'tp': position['tp'],
                            'lot_size': position['lot_size'],
                            'entry_time': position['entry_time'],
                            'close_time': None,
                            'symbol': sym,
                            'timeframe': position['timeframe'],
                            'profit': position['profit'],
                            'reason': position.get('reason', 'Manual/External Trade'),
                            'comments': position.get('comments', ''),
                            'status': 'open'
                        }
                        trades.append(trade)
                    
                    # Check all history categories
                    for history_list in [
                        self.trade_history[sym],
                        self.grid_history[sym],
                        self.suretrend_history[sym],
                        self.momentum_history[sym]
                    ]:
                        trades.extend([t for t in history_list if t.get('ticket') == ticket])
                    
                    # Get MT5 history for the ticket
                    if not self.simulate:
                        mt5_history = mt5.history_deals_get(ticket=ticket)
                        if mt5_history:
                            for deal in mt5_history:
                                if not any(t.get('ticket') == deal.ticket for t in trades):
                                    trades.append({
                                        'ticket': deal.ticket,
                                        'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                        'entry_price': deal.price,
                                        'close_price': deal.price,
                                        'sl': 0.0,
                                        'tp': 0.0,
                                        'lot_size': deal.volume,
                                        'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'symbol': deal.symbol,
                                        'timeframe': 'M1',
                                        'profit': deal.profit,
                                        'reason': 'External MT5 Trade',
                                        'comments': deal.comment,
                                        'status': 'closed'
                                    })
                    
            elif symbol:
                # For symbol-specific report
                title = f"TRADE REPORT {symbol}"
                # Include current open positions
                for pos in self.positions[symbol].values():
                    trades.append({
                        'ticket': pos['ticket'],
                        'type': "BUY" if pos['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                        'entry_price': pos['entry_price'],
                        'close_price': None,
                        'sl': pos['sl'],
                        'tp': pos['tp'],
                        'lot_size': pos['lot_size'],
                        'entry_time': pos['entry_time'],
                        'close_time': None,
                        'symbol': symbol,
                        'timeframe': pos['timeframe'],
                        'profit': pos['profit'],
                        'reason': pos.get('reason', 'Manual/External Trade'),
                        'comments': pos.get('comments', ''),
                        'status': 'open'
                    })
                
                # Add all historical trades
                trades.extend(self.trade_history[symbol])
                trades.extend(self.grid_history[symbol])
                trades.extend(self.suretrend_history[symbol])
                trades.extend(self.momentum_history[symbol])
                
                # Get MT5 history for the symbol
                if not self.simulate:
                    mt5_history = mt5.history_deals_get(
                        datetime.now() - timedelta(days=7),
                        datetime.now(),
                        symbol=symbol
                    )
                    if mt5_history:
                        for deal in mt5_history:
                            if not any(t.get('ticket') == deal.ticket for t in trades):
                                trades.append({
                                    'ticket': deal.ticket,
                                    'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                    'entry_price': deal.price,
                                    'close_price': deal.price,
                                    'sl': 0.0,
                                    'tp': 0.0,
                                    'lot_size': deal.volume,
                                    'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                    'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                    'symbol': symbol,
                                    'timeframe': 'M1',
                                    'profit': deal.profit,
                                    'reason': 'External MT5 Trade',
                                    'comments': deal.comment,
                                    'status': 'closed'
                                })
                    
            elif daily:
                # For daily report
                title = f"DAILY TRADE REPORT {datetime.now().strftime('%Y-%m-%d')}"
                today = datetime.now().date()
                
                for sym in self.symbols:
                    # Include current open positions opened today
                    for pos in self.positions[sym].values():
                        if self.parse_trade_time(pos['entry_time']).date() == today:
                            trades.append({
                                'ticket': pos['ticket'],
                                'type': "BUY" if pos['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                                'entry_price': pos['entry_price'],
                                'close_price': None,
                                'sl': pos['sl'],
                                'tp': pos['tp'],
                                'lot_size': pos['lot_size'],
                                'entry_time': pos['entry_time'],
                                'close_time': None,
                                'symbol': sym,
                                'timeframe': pos['timeframe'],
                                'profit': pos['profit'],
                                'reason': pos.get('reason', 'Manual/External Trade'),
                                'comments': pos.get('comments', ''),
                                'status': 'open'
                            })
                    
                    # Add all historical trades from today
                    for history_list in [
                        self.trade_history[sym],
                        self.grid_history[sym],
                        self.suretrend_history[sym],
                        self.momentum_history[sym]
                    ]:
                        trades.extend([t for t in history_list 
                                     if self.parse_trade_time(t.get('entry_time', '')).date() == today])
                    
                    # Get today's MT5 history
                    if not self.simulate:
                        today_start = datetime.combine(today, datetime.min.time())
                        mt5_history = mt5.history_deals_get(today_start, datetime.now(), symbol=sym)
                        if mt5_history:
                            for deal in mt5_history:
                                if not any(t.get('ticket') == deal.ticket for t in trades):
                                    trades.append({
                                        'ticket': deal.ticket,
                                        'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                        'entry_price': deal.price,
                                        'close_price': deal.price,
                                        'sl': 0.0,
                                        'tp': 0.0,
                                        'lot_size': deal.volume,
                                        'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'symbol': sym,
                                        'timeframe': 'M1',
                                        'profit': deal.profit,
                                        'reason': 'External MT5 Trade',
                                        'comments': deal.comment,
                                        'status': 'closed'
                                    })
            
            if not trades:
                return "No trades found for the specified criteria."
        
            # Add title
            story.append(Paragraph(title, ParagraphStyle('Title', fontSize=14, spaceAfter=20)))
            
            # Process trades
            for trade in trades:
                try:
                    # Get timeframe (handle both string and numeric formats)
                    trade_tf = trade.get('timeframe')
                    if isinstance(trade_tf, str):
                        timeframe = self.parse_timeframe(trade_tf)
                        tf_name = trade_tf
                    else:
                        timeframe = trade_tf
                        tf_name = self.get_timeframe_name(trade_tf)
                    
                    if not timeframe:
                        # If timeframe is invalid or missing, try to determine from trade history
                        time_diff = None
                        if trade.get('entry_time') and trade.get('close_time'):
                            entry = self.parse_trade_time(trade['entry_time'])
                            close = self.parse_trade_time(trade['close_time'])
                            time_diff = (close - entry).total_seconds()
                        
                        # Assign appropriate timeframe based on trade duration
                        if time_diff:
                            if time_diff <= 3600:  # 1 hour or less
                                timeframe = mt5.TIMEFRAME_M5
                                tf_name = 'M5'
                            elif time_diff <= 14400:  # 4 hours or less
                                timeframe = mt5.TIMEFRAME_M15
                                tf_name = 'M15'
                            else:
                                timeframe = mt5.TIMEFRAME_H1
                                tf_name = 'H1'
                        else:
                            # Default to M5 if can't determine
                            timeframe = mt5.TIMEFRAME_M5
                            tf_name = 'M5'
                    
                    # Trade placed details
                    trade_type = "Buy" if trade.get('type') == "BUY" else "Sell"
                    entry_details = (
                        f"Trade Placed: {trade_type} {trade.get('symbol', '')} {tf_name} "
                        f"Ticket no{trade.get('ticket', '')} placed {trade.get('entry_price', 0.0):.5f} "
                        f"due to {trade.get('reason', 'N/A')}"
                    )
                    story.append(Paragraph(entry_details, ParagraphStyle('Normal', spaceBefore=10)))
                    
                    # Add chart for the trade
                    symbol = trade.get('symbol')
                    entry_time = self.parse_trade_time(trade.get('entry_time', ''))
                    
                    # Get historical data around the trade time with appropriate timeframe
                    df = self.get_rates(symbol, timeframe=timeframe)
                    if df is not None:
                        df = self.calculate_indicators(df, timeframe, symbol)
                        
                        # Calculate Parabolic SAR and MACD using TA-Lib
                        import talib
                        import numpy as np
                        
                        # Ensure sufficient data for indicators
                        if len(df) < 26:  # Minimum for MACD slow EMA
                            self.logger.warning(f"Insufficient data for indicators on {symbol} {tf_name}: {len(df)} rows")
                            story.append(Paragraph(f"Insufficient data for indicators for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Convert to NumPy arrays for TA-Lib
                        high = np.array(df['high'], dtype=float)
                        low = np.array(df['low'], dtype=float)
                        close = np.array(df['close'], dtype=float)
                        
                        # Parabolic SAR
                        df['sar'] = talib.SAR(high, low, acceleration=0.02, maximum=0.2)
                        
                        # MACD
                        macd, macd_signal, macd_hist = talib.MACD(
                            close,
                            fastperiod=12,
                            slowperiod=26,
                            signalperiod=9
                        )
                        df['macd'] = macd
                        df['macd_signal'] = macd_signal
                        df['macd_hist'] = macd_hist
                        
                        # Create figure with subplots (main chart + MACD)
                        from plotly.subplots import make_subplots
                        fig = make_subplots(
                            rows=2, cols=1,
                            row_heights=[0.7, 0.3],
                            shared_xaxes=True,
                            vertical_spacing=0.1,
                            subplot_titles=[f"{symbol} {tf_name} Trade Chart", "MACD"]
                        )
                        
                        # Add candlestick chart to main plot (row 1)
                        fig.add_trace(
                            go.Candlestick(
                                x=df['time'],
                                open=df['open'],
                                high=df['high'],
                                low=df['low'],
                                close=df['close'],
                                name='OHLC'
                            ),
                            row=1, col=1
                        )
                        
                        # Add moving averages to main plot
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['ma_fast'],
                                mode='lines',
                                name=f'MA {self.ma_configs[timeframe]["fast"]}',
                                line=dict(color='blue')
                            ),
                            row=1, col=1
                        )
                        
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['ma_slow'],
                                mode='lines',
                                name=f'MA {self.ma_configs[timeframe]["slow"]}',
                                line=dict(color='red')
                            ),
                            row=1, col=1
                        )
                        
                        # Add Parabolic SAR to main plot
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['sar'],
                                mode='markers',
                                name='Parabolic SAR',
                                marker=dict(symbol='circle', size=5, color='purple')
                            ),
                            row=1, col=1
                        )
                        
                        # Add entry and exit points to main plot
                        entry_price = trade.get('entry_price')
                        exit_price = trade.get('close_price')
                        
                        fig.add_hline(y=entry_price, line_dash="dash", line_color="blue", annotation_text="Entry", row=1)
                        if exit_price:
                            fig.add_hline(y=exit_price, line_dash="dash", line_color="red", annotation_text="Exit", row=1)
                        
                        # Add SL/TP lines if available to main plot
                        if trade.get('sl'):
                            fig.add_hline(y=trade['sl'], line_dash="dot", line_color="red", annotation_text="SL", row=1)
                        if trade.get('tp'):
                            fig.add_hline(y=trade['tp'], line_dash="dot", line_color="green", annotation_text="TP", row=1)
                        
                        # Add MACD to subplot (row 2)
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['macd'],
                                mode='lines',
                                name='MACD',
                                line=dict(color='blue')
                            ),
                            row=2, col=1
                        )
                        
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['macd_signal'],
                                mode='lines',
                                name='Signal',
                                line=dict(color='orange')
                            ),
                            row=2, col=1
                        )
                        
                        fig.add_trace(
                            go.Bar(
                                x=df['time'],
                                y=df['macd_hist'],
                                name='Histogram',
                                marker_color=df['macd_hist'].apply(lambda x: 'green' if x >= 0 else 'red')
                            ),
                            row=2, col=1
                        )
                        
                        # Add profit annotation to main plot
                        if trade.get('profit_points'):
                            fig.add_annotation(
                                x=df['time'].iloc[-1],
                                y=exit_price or df['close'].iloc[-1],
                                text=f"Profit: {trade.get('profit_points', 0):.2f} points",
                                showarrow=True,
                                arrowhead=1,
                                row=1, col=1
                            )
                        
                        # Update layout
                        fig.update_layout(
                            height=500,
                            margin=dict(l=50, r=50, t=50, b=50),
                            showlegend=True,
                            xaxis2=dict(title='Time'),
                            yaxis=dict(title='Price'),
                            yaxis2=dict(title='MACD')
                        )
                        
                        # Save chart as temporary image with absolute path
                        temp_chart = os.path.join(self.reports_folder, f"temp_chart_{trade.get('ticket')}.png")
                        try:
                            self.logger.debug(f"Attempting to write chart to {temp_chart}")
                            fig.write_image(temp_chart, engine="kaleido")
                            self.logger.debug(f"Chart written to {temp_chart}")
                        except Exception as e:
                            self.logger.error(f"Failed to write chart image {temp_chart}: {str(e)}")
                            story.append(Paragraph(f"Chart generation failed for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Verify file exists before adding to PDF
                        if not os.path.exists(temp_chart):
                            self.logger.error(f"Chart image {temp_chart} was not created.")
                            story.append(Paragraph(f"Chart missing for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Add chart to PDF
                        try:
                            img = Image(temp_chart)
                            img.drawHeight = 350
                            img.drawWidth = 500
                            story.append(img)
                            story.append(Spacer(1, 20))
                        except Exception as e:
                            self.logger.error(f"Failed to add chart {temp_chart} to PDF: {str(e)}")
                            story.append(Paragraph(f"Chart inclusion failed for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Clean up temporary file
                        try:
                            os.remove(temp_chart)
                            self.logger.debug(f"Deleted temporary chart {temp_chart}")
                        except Exception as e:
                            self.logger.warning(f"Failed to delete temporary chart {temp_chart}: {str(e)}")
                    
                    # Add SL/TP details
                    sl_tp_details = (
                        f"Initial SL: {trade.get('sl', 'N/A'):.5f}, "
                        f"TP: {trade.get('tp', 'N/A'):.5f}"
                    )
                    story.append(Paragraph(sl_tp_details, ParagraphStyle('Normal', leftIndent=20)))
                    
                    # Add close details if trade is closed
                    if trade.get('close_time'):
                        close_details = (
                            f"Trade Closed: The trade {trade_type} {trade.get('symbol', '')} {tf_name} "
                            f"Ticket no{trade.get('ticket', '')} was closed at {trade.get('close_time', '')} "
                            f"due to {trade.get('close_reason', 'N/A')}"
                        )
                        story.append(Paragraph(close_details, ParagraphStyle('Normal', spaceBefore=10)))
                    
                    story.append(Spacer(1, 20))
                    
                except Exception as e:
                    self.logger.error(f"Error processing trade {trade.get('ticket', 'unknown')}: {str(e)}")
                    continue
            
            # Build PDF
            doc.build(story)
            
            # Send report via Telegram if available
            if self.TELEGRAM_BOT_TOKEN and self.TELEGRAM_CHAT_ID:
                try:
                    with open(filepath, 'rb') as f:
                        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendDocument"
                        files = {'document': f}
                        data = {'chat_id': self.TELEGRAM_CHAT_ID}
                        response = requests.post(url, data=data, files=files)
                        if not response.json().get('ok'):
                            self.logger.error(f"Failed to send report via Telegram: {response.json()}")
                except Exception as e:
                    self.logger.error(f"Error sending report via Telegram: {str(e)}")
            
            return f"Report generated successfully: {filepath}"
            
        except Exception as e:
            self.logger.error(f"Error generating trade report: {str(e)}")
            return f"Failed to generate report: {str(e)}"
    
    def parse_trade_time(self, time_str):
        """Parse trade time string handling both formats with and without microseconds."""
        try:
            # Try parsing with microseconds
            return datetime.strptime(time_str, '%Y-%m-%d %H:%M:%S.%f')
        except ValueError:
            try:
                # Try parsing without microseconds
                return datetime.strptime(time_str, '%Y-%m-%d %H:%M:%S')
            except ValueError:
                # Return current time if parsing fails
                self.logger.error(f"Failed to parse time string: {time_str}")
                return datetime.now()

    def convert_to_points(self, profit, symbol):
        """Enhanced conversion of profit to points with proper null handling."""
        try:
            if profit is None or self.point.get(symbol) is None:
                return 0.0
            
            # Get lot size from position if available, otherwise use default
            lot_size = getattr(self, 'lot_size', 0.1)  # Default to 0.1 if not set
            point_value = self.point[symbol] * lot_size * 10000
            
            # Avoid division by zero
            if point_value == 0:
                return 0.0
            
            return profit / point_value
        except Exception as e:
            self.logger.debug(f"Error converting profit to points: {str(e)}")
            return 0.0

    def update_trade_history_on_close(self, ticket, symbol, profit_points, reason):
        """Enhanced trade history update with better error handling"""
        try:
            with self.command_lock:
                close_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f')
                
                # Safely calculate actual profit
                try:
                    point_value = self.point.get(symbol, 0.0)
                    lot_size = getattr(self, 'lot_size', 0.1)
                    actual_profit = profit_points * point_value * lot_size * 10000 if all(v is not None for v in [profit_points, point_value, lot_size]) else 0.0
                except Exception as e:
                    self.logger.debug(f"Error calculating actual profit: {str(e)}")
                    actual_profit = 0.0
                
                # Update profit and close time in all history lists
                for history in [self.trade_history, self.grid_history, self.suretrend_history, self.momentum_history]:
                    if symbol in history:
                        for trade in history[symbol]:
                            try:
                                if trade.get('ticket') == ticket:
                                    trade['profit'] = actual_profit
                                    trade['profit_points'] = profit_points
                                    trade['close_time'] = close_time
                                    trade['close_reason'] = reason
                                    trade['status'] = 'closed'
                                    break
                            except Exception as e:
                                self.logger.debug(f"Error updating trade {ticket}: {str(e)}")
                            continue
                
                self.save_trade_history()
                
        except Exception as e:
            self.logger.error(f"Error updating trade history on close: {str(e)}")

    def get_rates(self, symbol, num_candles=100, timeframe=None):
        """Enhanced rate retrieval with better error handling"""
        if self.simulate:
            return self.get_simulated_rates(symbol, num_candles, timeframe)
        
        retry_count = 0
        while retry_count < self.max_retries:
            try:
                # First ensure MT5 is initialized
                if not self.ensure_mt5_connection():
                    raise Exception("Failed to ensure MT5 connection")
                
                # Convert string timeframe to MT5 timeframe constant if needed
                if isinstance(timeframe, str):
                    timeframe = self.timeframe_configs.get(timeframe.upper())
                    if timeframe is None:
                        raise Exception(f"Invalid timeframe string: {timeframe}")
                
                # Verify timeframe is valid
                valid_timeframes = [mt5.TIMEFRAME_M1, mt5.TIMEFRAME_M5, mt5.TIMEFRAME_M15, 
                                  mt5.TIMEFRAME_M30, mt5.TIMEFRAME_H1, mt5.TIMEFRAME_H4]
                if timeframe not in valid_timeframes:
                    raise Exception(f"Invalid timeframe value: {timeframe}")
                
                # Get rates with explicit error checking
                rates = mt5.copy_rates_from_pos(symbol, timeframe, 0, max(num_candles, 100))  # Always get at least 100 candles
                if rates is None:
                    error = mt5.last_error()
                    raise Exception(f"copy_rates_from_pos failed: {error}")
                
                if len(rates) == 0:
                    raise Exception("No rates returned")
                
                # Convert to DataFrame
                df = pd.DataFrame(rates)
                df['time'] = pd.to_datetime(df['time'], unit='s')
                
                # Cache the data
                if symbol in self.data_cache and timeframe in self.data_cache[symbol]:
                    self.data_cache[symbol][timeframe]['df'] = df
                    self.data_cache[symbol][timeframe]['last_time'] = df['time'].iloc[-1]
                
                self.logger.debug(f"[{symbol}] Successfully retrieved {len(df)} candles for {self.get_timeframe_name(timeframe)}")
                return df
                
            except Exception as e:
                retry_count += 1
                self.logger.error(f"[{symbol}] Failed to get rates (attempt {retry_count}/{self.max_retries}): {str(e)}")
                
                if retry_count < self.max_retries:
                    sleep_time = min(300, self.retry_delay * (2 ** (retry_count - 1)) + random.uniform(0, 1))
                    self.logger.info(f"[{symbol}] Waiting {sleep_time:.1f} seconds before retry...")
                    time.sleep(sleep_time)
                    
                    # Try to use cached data if available
                    if symbol in self.data_cache and timeframe in self.data_cache[symbol]:
                        cached_df = self.data_cache[symbol][timeframe]['df']
                        if cached_df is not None and len(cached_df) > 0:
                            self.logger.warning(f"[{symbol}] Using cached data due to rate retrieval failure")
                            return cached_df
                else:
                    self.logger.error(f"[{symbol}] Failed to get rates after {self.max_retries} attempts")
                    # Try one last time to use cached data
                    if symbol in self.data_cache and timeframe in self.data_cache[symbol]:
                        cached_df = self.data_cache[symbol][timeframe]['df']
                        if cached_df is not None and len(cached_df) > 0:
                            self.logger.warning(f"[{symbol}] Using cached data as final fallback")
                            return cached_df
        
        return None

    def save_lock_state(self):
        """Save trading lock state to file."""
        try:
            lock_data = {
                'locked': self.trading_locked,
                'reason': self.trading_lock_reason,
                'date': datetime.now().strftime('%Y-%m-%d')
            }
            with open(self.lock_file, 'w') as f:
                json.dump(lock_data, f)
        except Exception as e:
            self.logger.error(f"Error saving lock state: {str(e)}")

    def __init__(self, mt5_login=None, mt5_password=None, mt5_server=None, symbols=None, timeframes=None, lot_size=0.1, daily_max_profit=500, simulate=False, risk_percent=2.0, mt5_path=None):
        # Initialize trading lock state before other attributes
        self.trading_locked = False
        self.lock_reason = None
        
        # Add SureTrend tracking attributes
        self.suretrend_tracking = {
            symbol: {
                tf: {
                    'conditions_met': False,
                    'signal_type': None,  # 'buy' or 'sell'
                    'start_time': None,
                    'start_price': None,
                    'current_deviation': 0,
                    'ma_invalidated': False,
                    'duration': 0,
                    'conditions': {
                        'trend_aligned': False,
                        'momentum_confirmed': False,
                        'volatility_suitable': False,
                        'ma_alignment': False
                    }
                } for tf in (timeframes or [])
            } for symbol in (symbols or [])
        }
        
        # Create monitoring control attributes
        self.stop_monitoring = threading.Event()
        self.monitoring_thread = None
        
        # Continue with existing initialization
        self.mt5_login = mt5_login
        self.mt5_password = mt5_password
        self.mt5_server = mt5_server
        self.symbols = symbols or []
        self.timeframes = timeframes or []
        self.lot_size = lot_size
        self.daily_max_profit = daily_max_profit
        self.simulate = simulate
        self.risk_percent = risk_percent
        self.mt5_path = mt5_path
        
        self.mt5_connected = False
        self.mt5_account_info = None
        self.mt5_account_balance = 0
        self.mt5_account_equity = 0
        self.mt5_account_margin = 0
        self.mt5_account_free_margin = 0
        self.mt5_account_margin_level = 0
        self.mt5_account_margin_free = 0
        self.mt5_account_margin_level = 0
        self.mt5_account_margin_so = 0
        self.mt5_account_margin_so_call = 0
        self.mt5_account_margin_so_mode = 0
        self.mt5_account_margin_so_mode_text = ""
        self.mt5_account_margin_so_mode_color = ""
        self.mt5_account_margin_so_mode_text_color = ""
        self.mt5_account_margin_so_mode_bg_color = ""
        self.mt5_account_margin_so_mode_border_color = ""
        self.mt5_account_margin_so_mode_border_width = 0
        self.mt5_account_margin_so_mode_border_style = ""
        self.mt5_account_margin_so_mode_border_radius = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
        self.mt5_account_margin_so_mode_border_radius_left = 0
        self.mt5_account_margin_so_mode_border_radius_right = 0
        self.mt5_account_margin_so_mode_border_radius_all = 0
        self.mt5_account_margin_so_mode_border_radius_top_left = 0
        self.mt5_account_margin_so_mode_border_radius_top_right = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_left = 0
        self.mt5_account_margin_so_mode_border_radius_bottom_right = 0
        self.mt5_account_margin_so_mode_border_radius_top = 0
        self.mt5_account_margin_so_mode_border_radius_bottom = 0
#python start3.py --mt5-login 61339636 --mt5-password "Neema@#54" --mt5-server "Pepperstone-Demo" --symbols XAUUSD EURUSD US500 NAS100 USDJPY --timeframes M1 M5 M15 M30 H1 H4  --lot-size 0.2 --daily-max-profit 1000  --risk-percent 1.5
#python start3.py --mt5-login 61339636 --mt5-password "Neema@#54" --mt5-server "Pepperstone-Demo" --symbols XAUUSD --timeframes M1 M5 --lot-size 0.2 --daily-max-profit 1000  --risk-percent 1.5
import os
import sys
import time
import shutil
import json
import queue
import random
import logging
import warnings
import threading
import argparse
import subprocess
import MetaTrader5 as mt5
from datetime import datetime, timedelta
import pandas as pd
import numpy as np
import plotly.graph_objects as go
import re
import requests
import keyboard
import colorlog
import talib
import psutil
import atexit
from reportlab.lib import colors
from reportlab.lib.pagesizes import letter
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Image, Table, TableStyle
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from prompt_toolkit import PromptSession
from prompt_toolkit.completion import WordCompleter
from prompt_toolkit.history import InMemoryHistory
from concurrent.futures import ThreadPoolExecutor
import tempfile
import shutil
from tqdm import tqdm

warnings.filterwarnings("ignore", category=UserWarning, message="Pandas doesn't allow columns to be created via a new attribute name")

class TradingStrategy:
    def __init__(self, mt5_login=None, mt5_password=None, mt5_server=None, symbols=None, timeframes=None, lot_size=0.1, daily_max_profit=500, simulate=False, risk_percent=2.0, mt5_path=None):
        # Initialize trading lock state before other attributes
        self.trading_locked = False
        self.trading_lock_reason = ""
        # Setup logging first       
        self._setup_logging()
        self.simulate = False
        # Add drawdown tracking attributes
        self.balance_file = "daily_balance.json"
        self.max_drawdown_percent = 50  # 50% maximum drawdown
        self.initial_balance = None
        self.lowest_balance = None
        self.load_daily_balance()
        self.initialize_daily_balance()
        self.mt5_login = mt5_login or 61318849
        self.mt5_password = mt5_password or "Neema@#54"
        self.mt5_server = mt5_server or "Pepperstone-Demo"
            # Initialize status update thread
        self.status_update_interval = 1  # Update every second
        self.status_thread_running = True
        self.status_thread = threading.Thread(target=self.status_update_loop, daemon=True)
        self.status_thread.start()
        
        # Initialize mock trade manager
        self.mock_trade_manager = MockTradeManager(self)

        # Add market check intervals
        self.market_check_interval = 60  # Check market status every 60 seconds
        self.market_closed_sleep = 300   # Sleep for 5 minutes when market is closed

        self.ADMIN_PASSWORD = "TR@d3L3@d3r2025#"  # Complex password for admin override
        self.max_daily_loss = -500  # Set maximum daily loss in points (negative value)
        # Add lock file path
        self.lock_file = "trading_lock.json"
        # Load lock state from file
        self.load_lock_state()

        # Add report generation folder
        self.reports_folder = "trade_reports"
        os.makedirs(self.reports_folder, exist_ok=True)
        
        # Register Times New Roman font
        pdfmetrics.registerFont(TTFont('Times-Roman', 'times.ttf'))
        self.accounts = {
            'default': {'login': self.mt5_login, 'password': self.mt5_password, 'server': self.mt5_server}
        }
        self.current_account = 'default'
        self.sync_enabled = False

        self.TELEGRAM_BOT_TOKEN = "7135089206:AAEmnAztKDkjXg5jM4dXbrjfF3dCvcwJ9Ow"
        self.TELEGRAM_CHAT_ID = "6178394807"
        self.telegram_offset = 0

        self.symbols = symbols if symbols is not None else ['XAUUSD']

        # Initialize symbol_info dictionary
        self.symbol_info = {symbol: {} for symbol in self.symbols}
        self.point = {symbol: None for symbol in self.symbols}

        # Define timeframe_configs before using it in parse_timeframe
        self.timeframe_configs = {
            'M1': mt5.TIMEFRAME_M1, 'M5': mt5.TIMEFRAME_M5, 'M15': mt5.TIMEFRAME_M15,
            'M30': mt5.TIMEFRAME_M30, 'H1': mt5.TIMEFRAME_H1, 'H4': mt5.TIMEFRAME_H4
        }
        # Now parse timeframes after timeframe_configs is defined
        self.timeframes = [self.parse_timeframe(tf) for tf in (timeframes or ['M1'])]

        self.timeframe_intervals = {
            mt5.TIMEFRAME_M1: 60, mt5.TIMEFRAME_M5: 300, mt5.TIMEFRAME_M15: 900,
            mt5.TIMEFRAME_M30: 1800, mt5.TIMEFRAME_H1: 3600, mt5.TIMEFRAME_H4: 14400
        }

        self.lot_size = lot_size
        self.deviation = 10

        self.lot_size = lot_size
        self.deviation = 10  # Adjusted to match second half
        self.max_retries = 3
        self.retry_delay = 5
        self.simulate = simulate
        self.risk_percent = risk_percent
        self.daily_max_profit = daily_max_profit

        self.primary_strategy_enabled = True
        self.suretrend_automation_enabled = False
        self.grid_trading_enabled = False
        self.grid_automation_enabled = False
        self.momentum_automation_enabled = False  # Removed momentum_enabled, using automation flag only

        self.grid_levels = 5
        self.grid_spacing = 10

        self.ma_configs = {
            tf: {'fast': 3 if tf in [mt5.TIMEFRAME_M1, mt5.TIMEFRAME_M5] else 5,
                 'slow': 8 if tf in [mt5.TIMEFRAME_M1, mt5.TIMEFRAME_M5] else 10,
                 'exit_fast': 5, 'exit_slow': 10}
            for tf in self.timeframes  # Changed to self.timeframes for consistency
        }
        self.macd_fast, self.macd_slow, self.macd_signal = 12, 26, 9
        self.momentum_period = 14
        self.psar_step, self.psar_max = 0.02, 0.2
        self.bollinger_period, self.bollinger_dev = 20, 2
        self.atr_period = 14

        self.breakeven_configs = {tf: 50.0 for tf in self.timeframes}
        self.trailing_stop_configs = {tf: 50.0 for tf in self.timeframes}
        self.trailing_delay_configs = {tf: 50.0 for tf in self.timeframes}
        self.signal_cooldown = 300  # 5 minutes default, matching second half
        self.initial_sl = 200  # Default SL in points, matching second half
        #self.initial_balance = 1000
        self.dynamic_management_enabled = False  # Aligned with second half default
        self.exit_signals_enabled = True
        self.use_m5_exit = False

        self.positions = {symbol: {} for symbol in self.symbols}
        self.daily_profit = {symbol: 0.0 for symbol in self.symbols}
        self.daily_trades = {symbol: [] for symbol in self.symbols}  # Simplified to list per symbol
        self.trade_history = {symbol: [] for symbol in self.symbols}
        self.grid_history = {symbol: [] for symbol in self.symbols}
        self.suretrend_history = {symbol: [] for symbol in self.symbols}
        self.momentum_history = {symbol: [] for symbol in self.symbols}
        self.trading_allowed = {symbol: True for symbol in self.symbols}
        self.last_check_times = {symbol: {tf: datetime.now() for tf in self.timeframes} for symbol in self.symbols}
        self.last_signal_times = {symbol: {tf: datetime.now() - timedelta(seconds=self.signal_cooldown) for tf in self.timeframes} for symbol in self.symbols}
        self.waiting_for_trade_confirmation = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.trade_confirmation_queue = queue.Queue()
        self.command_lock = threading.Lock()
        self.context_symbol = None
        self.threads = []
        self.symbol_terminal_threads = {}

        # Initialize ma_exit_enabled with both string and numeric timeframe keys
        self.ma_exit_enabled = {}
        for symbol in self.symbols:
            self.ma_exit_enabled[symbol] = {}
            for tf in self.timeframes:
                # Add numeric timeframe key
                self.ma_exit_enabled[symbol][tf] = False
                # Add string timeframe key
                tf_name = self.get_timeframe_name(tf)
                self.ma_exit_enabled[symbol][tf_name] = False
                # Special case for M5
                if tf_name == 'M5':
                    self.ma_exit_enabled[symbol][tf_name] = self.use_m5_exit

        self.volatility_check_enabled = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.psar_filter_enabled = {symbol: {tf: False for tf in self.timeframes} for symbol in self.symbols}
        self.psar_filter_timeframe = {symbol: {tf: mt5.TIMEFRAME_H1 for tf in self.timeframes} for symbol in self.symbols}
        self.data_cache = {symbol: {tf: {'df': None, 'last_time': None} for tf in self.timeframes} for symbol in self.symbols}
        self.suretrend_conditions_met = {symbol: {tf: {'buy': False, 'sell': False} for tf in self.timeframes} for symbol in self.symbols}
        self.trades_per_strategy = {symbol: {tf: {"primary": 0, "suretrend": 0, "grid": 0, "momentum": 0, "breakout_momentum": 0} for tf in self.timeframes} for symbol in self.symbols}

        self._setup_logging()
        self.load_trade_history()
        atexit.register(self.cleanup)
        keyboard.on_press_key("q", self.handle_exit)

        # Enhanced error handling settings
        self.max_consecutive_errors = 3
        self.error_cooldown = 60  # seconds
        self.last_error_time = None
        self.consecutive_errors = 0
        
        # Load saved Telegram offset
        self.load_telegram_offset()
        
        # Initialize connection status
        self.mt5_connected = False
        self.telegram_connected = False

        # Add semi-automated mode variables
        self.primary_strategy_semi_auto = False
        self.suretrend_semi_auto = False
        self.grid_semi_auto = False
        self.momentum_semi_auto = False

        # Add MT5 path to the initialization
        self.mt5_path = mt5_path or r"C:\Program Files\MetaTrader 5\terminal64.exe"

        # Add new sync-related attributes
        self.sync_interval = 1  # Sync every 1 second
        self.last_sync_time = datetime.now()
        self.last_known_positions = {symbol: {} for symbol in self.symbols}
        self.last_known_history = {symbol: set() for symbol in self.symbols}
        self.external_trade_defaults = {
            'sl_points': 200,  # Default SL in points
            'tp_ratio': 2.0,   # TP = SL * tp_ratio
            'timeframe': mt5.TIMEFRAME_M1  # Default timeframe for external trades
        }
        
        # Start continuous sync thread
        self.sync_thread = threading.Thread(target=self.continuous_sync_loop, daemon=True)
        self.sync_thread.start()

        # Add HFScalper strategy attributes
        self.hfscalper_enabled = False
        self.hfscalper_semi_auto = False
        self.hfscalper_min_momentum = 0.0001
        self.hfscalper_volatility_threshold = 1.5
        self.hfscalper_tp_points = 10
        self.hfscalper_psar_enabled = False
        self.hfscalper_psar_step = 0.02
        self.hfscalper_psar_max = 0.2
        self.hfscalper_history = {symbol: [] for symbol in (symbols or ['XAUUSD'])}

        self.breakout_momentum_enabled = False
        self.breakout_momentum_semi_auto = False
        self.breakout_momentum_history = {symbol: [] for symbol in self.symbols}
        self.rsi_period = 14  # RSI period for overbought/oversold detection
        self.rsi_overbought = 70
        self.rsi_oversold = 30
        self.consolidation_lookback = 20  # Lookback period for consolidation detection
        self.consolidation_threshold = 0.05  # BB width threshold for consolidation
        self.breakout_multiplier = 1.5  # TP multiplier based on consolidation range
        self.atr_multiplier_sl = 1.5  # SL multiplier based on ATR
        self.atr_multiplier_trailing = 1.0  # Trailing stop multiplier

        # Add new signal optimization attributes
        self.signal_optimization_enabled = False
        self.realtime_signals_enabled = True
        self.signal_quality_threshold = 0.7
        self.signal_interval = 1  # seconds
        self.signal_history = {symbol: {tf: [] for tf in self.timeframes} for symbol in self.symbols}
        self.signal_performance = {symbol: {tf: {'total': 0, 'successful': 0} for tf in self.timeframes} for symbol in self.symbols}
        self.signal_alerts_enabled = True
        self.signal_logging_enabled = True
        self.signal_filters = {
            'momentum_threshold': 0.0001,
            'volatility_threshold': 1.5,
            'min_confirmation_signals': 2,
            'min_signal_quality': 0.7
        }
        
        self.strategy_performance = {
            'primary': {'total': 0, 'successful': 0, 'profit': 0.0},
            'suretrend': {'total': 0, 'successful': 0, 'profit': 0.0},
            'grid': {'total': 0, 'successful': 0, 'profit': 0.0},
            'momentum': {'total': 0, 'successful': 0, 'profit': 0.0},
            'hfscalper': {'total': 0, 'successful': 0, 'profit': 0.0},
            'breakout_momentum': {'total': 0, 'successful': 0, 'profit': 0.0}
        }
        
        # Signal quality metrics
        self.signal_quality_metrics = {
            'accuracy': 0.0,
            'profit_factor': 0.0,
            'win_rate': 0.0,
            'avg_profit': 0.0,
            'avg_loss': 0.0
        }

        # Add SureTrend tracking attributes
        self.suretrend_tracking = {
            symbol: {
                tf: {
                    'conditions_met': False,
                    'signal_type': None,  # 'buy' or 'sell'
                    'start_time': None,
                    'start_price': None,
                    'current_deviation': 0,
                    'ma_invalidated': False,
                    'duration': 0,
                    'conditions': {
                        'trend_aligned': False,
                        'momentum_confirmed': False,
                        'volatility_suitable': False,
                        'ma_alignment': False
                    }
                } for tf in (timeframes or [])
            } for symbol in (symbols or [])
        }
        
        # Create an event to signal monitoring thread to stop
        self.stop_monitoring = threading.Event()
        
        # Create a thread for background monitoring
        self.monitoring_thread = None

    def _setup_logging(self):
        log_folder = "live_trading_logs"
        os.makedirs(log_folder, exist_ok=True)
        log_file = os.path.join(log_folder, f"trading_log_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log")
        
        self.logger = logging.getLogger(__name__)
        self.logger.setLevel(logging.DEBUG)
        
        # Custom formatter using TerminalManager colors
        class ColoredFormatter(logging.Formatter):
            def format(self, record):
                if record.levelno >= logging.ERROR:
                    color = self.terminal.COLORS['red']
                elif record.levelno >= logging.WARNING:
                    color = self.terminal.COLORS['yellow']
                elif record.levelno >= logging.INFO:
                    color = self.terminal.COLORS['green']
                else:
                    color = self.terminal.COLORS['blue']
                
                record.msg = f"{color}{record.msg}{self.terminal.COLORS['reset']}"
                return super().format(record)
        
        # Set up handlers with the new formatter
        formatter = ColoredFormatter('%(asctime)s | %(levelname)s | %(message)s')
        
        # Console handler
        ch = logging.StreamHandler()
        ch.setFormatter(formatter)
        self.logger.addHandler(ch)
        
        # File handler
        fh = logging.FileHandler(log_file)
        fh.setFormatter(logging.Formatter('%(asctime)s | %(levelname)s | %(message)s'))
        self.logger.addHandler(fh)

    def update_status_line(self):
        """Update the status line with current system state."""
        try:
            # Get connection status
            mt5_status = "Connected" if self.mt5_connected else "Disconnected"
            telegram_status = "Connected" if self.telegram_connected else "Disconnected"
            
            # Get trade counts
            active_trades = sum(len(self.positions[s]) for s in self.symbols)
            mock_trades = len(self.mock_trade_manager.mock_trades)
            
            # Get profit
            daily_profit = sum(self.convert_to_points(self.daily_profit[s], s) for s in self.symbols)
            
            status = (
                f"Last Update: {datetime.now().strftime('%H:%M:%S')} | "
                f"MT5: {mt5_status} | Telegram: {telegram_status} | "
                f"Active Trades: {active_trades} | Mock Trades: {mock_trades} | "
                f"Daily Profit: {daily_profit:.1f} pts"
            )
            
            self.terminal.update_status(status)
        except Exception as e:
            self.logger.error(f"Error updating status line: {str(e)}")

    def parse_timeframe(self, tf_str):
        tf_str = tf_str.upper()
        return self.timeframe_configs.get(tf_str)

    def get_timeframe_name(self, timeframe):
        for name, value in self.timeframe_configs.items():
            if value == timeframe:
                return name
        return "Unknown"

    def get_telegram_updates(self):
        """Enhanced Telegram updates with proper offset handling and better timeout handling."""
        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/getUpdates"
        
        retry_count = 0
        while retry_count < self.max_retries:
            try:
                params = {
                    "offset": self.telegram_offset,
                    "timeout": 30,
                    "allowed_updates": ["message"]
                }
                
                # Increase timeout and add backoff strategy
                response = requests.get(url, params=params, timeout=60)
                response.raise_for_status()
                
                updates = response.json()
                if updates.get("ok") and "result" in updates:
                    if updates["result"]:
                        latest_update = max(update["update_id"] for update in updates["result"])
                        self.telegram_offset = latest_update + 1
                        self.save_telegram_offset()
                    return updates
                    
                time.sleep(1)
                
            except requests.exceptions.Timeout:
                retry_count += 1
                self.logger.warning(f"Telegram timeout (attempt {retry_count}/{self.max_retries}), retrying...")
                time.sleep(5 * retry_count)  # Progressive backoff
            except requests.exceptions.RequestException as e:
                retry_count += 1
                self.logger.error(f"Failed to get Telegram updates (attempt {retry_count}/{self.max_retries}): {str(e)}")
                if retry_count == self.max_retries:
                    time.sleep(60)
                    retry_count = 0
                else:
                    time.sleep(5 * retry_count)
        
        return None

    def save_telegram_offset(self):
        """Save Telegram offset to file."""
        try:
            with open("telegram_offset.txt", "w") as f:
                f.write(str(self.telegram_offset))
        except Exception as e:
            self.logger.error(f"Failed to save Telegram offset: {e}")

    def load_telegram_offset(self):
        """Load Telegram offset from file."""
        try:
            if os.path.exists("telegram_offset.txt"):
                with open("telegram_offset.txt", "r") as f:
                    self.telegram_offset = int(f.read().strip())
        except Exception as e:
            self.logger.error(f"Failed to load Telegram offset: {e}")

    def send_telegram_message(self, message, thread_id=None, chart_path=None, chat_id=None):
        """Enhanced Telegram message sending with better timeout handling"""
        if not self.TELEGRAM_BOT_TOKEN or not self.TELEGRAM_CHAT_ID:
            self.logger.warning("Telegram credentials not configured")
            return None

        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendMessage"
        max_length = 4096
        chat_id = chat_id or self.TELEGRAM_CHAT_ID
        
        # Format message
        formatted_message = f"> GC_Signals:\n{message}"
        formatted_message = formatted_message.replace('<', '&lt;').replace('>', '&gt;')
        
        # Split long messages
        if len(formatted_message) > max_length:
            parts = []
            current_part = "> GC_Signals:\n"
            for line in message.split('\n'):
                if len(current_part) + len(line) + 1 <= max_length:
                    current_part += line + '\n'
                else:
                    parts.append(current_part.strip())
                    current_part = f"> GC_Signals:\n{line}\n"
            if current_part:
                parts.append(current_part.strip())
        else:
            parts = [formatted_message]
        
        last_message_id = None
        for part in parts:
            retry_count = 0
            while retry_count < self.max_retries:
                try:
                    payload = {
                        "chat_id": chat_id,
                        "text": part,
                        "parse_mode": "HTML"
                    }
                    
                    if thread_id and not last_message_id:
                        payload["reply_to_message_id"] = thread_id
                    elif last_message_id:
                        payload["reply_to_message_id"] = last_message_id

                    response = requests.post(url, json=payload, timeout=30)  # Increased timeout
                    response.raise_for_status()
                    
                    result = response.json()
                    if not result.get("ok"):
                        raise Exception(f"Telegram API error: {result.get('description')}")
                        
                    last_message_id = result.get("result", {}).get("message_id")
                    
                    # Send chart if available
                    if chart_path and last_message_id and part == parts[-1]:
                        try:
                            with open(chart_path, 'rb') as chart_file:
                                files = {'photo': chart_file}
                                photo_url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendPhoto"
                                photo_response = requests.post(
                                    photo_url,
                                    data={"chat_id": chat_id, "reply_to_message_id": last_message_id},
                                    files=files,
                                    timeout=30  # Increased timeout
                                )
                                photo_response.raise_for_status()
                        except Exception as e:
                            self.logger.error(f"Failed to send chart: {e}")
                    
                    break
                    
                except Exception as e:
                    retry_count += 1
                    self.logger.error(f"Failed to send Telegram message (attempt {retry_count}/{self.max_retries}): {e}")
                    if retry_count == self.max_retries:
                        return None
                    time.sleep(5 * retry_count)  # Progressive backoff
        
        return last_message_id

    def load_trade_history(self):
        for symbol in self.symbols:
            for filename, history_dict in [
                (f"trade_history_{symbol}.json", self.trade_history),
                (f"grid_history_{symbol}.json", self.grid_history),
                (f"suretrend_history_{symbol}.json", self.suretrend_history),
                (f"momentum_history_{symbol}.json", self.momentum_history)
            ]:
                if os.path.exists(filename):
                    with open(filename, 'r') as f:
                        try:
                            history_dict[symbol] = json.load(f)
                            self.logger.info(f"[{symbol}] Loaded {len(history_dict[symbol])} trades from {filename}")
                        except json.JSONDecodeError:
                            self.logger.error(f"[{symbol}] Failed to load {filename}")

    def save_trade_history(self):
        for symbol in self.symbols:
            for filename, history_dict in [
                (f"trade_history_{symbol}.json", self.trade_history),
                (f"grid_history_{symbol}.json", self.grid_history),
                (f"suretrend_history_{symbol}.json", self.suretrend_history),
                (f"momentum_history_{symbol}.json", self.momentum_history)
            ]:
                with open(filename, 'w') as f:
                    json.dump(history_dict[symbol], f, default=str)

    def cleanup(self):
        self.logger.info("Cleaning up...")
        try:
            # Stop status thread
            self.status_thread_running = False
            if hasattr(self, 'status_thread'):
                self.status_thread.join(timeout=2)
            
            # Existing cleanup code...
            with self.command_lock:
                for symbol in self.symbols:
                    for position in list(self.positions[symbol].values()):
                        self.close_position(position, "System shutdown")
                self.save_trade_history()
                
            # Ensure proper MT5 shutdown
            if mt5.terminal_info():
                mt5.shutdown()
                
            # Additional cleanup for background terminal
            try:
                subprocess.run(['taskkill', '/F', '/IM', 'terminal64.exe'], capture_output=True)
            except Exception as e:
                self.logger.warning(f"Failed to force close MT5 terminal: {e}")
        except Exception as e:
            self.logger.error(f"Error during cleanup: {e}")

    def handle_exit(self, e):
        if e.name == 'q':
            self.cleanup()
            os._exit(0)

    def ensure_mt5_connection(self):
        """Enhanced MT5 connection handling with better retry logic"""
        if self.simulate:
            return True

        try:
            # First check if we're already connected
            if mt5.terminal_info() and mt5.account_info():
                return True

            # If not connected, try to initialize
            if not mt5.initialize():
                # Kill any existing MT5 processes first
                try:
                    import subprocess
                    import psutil
                    for proc in psutil.process_iter(['pid', 'name']):
                        try:
                            if proc.info['name'].lower() in ['terminal64.exe', 'metatrader.exe', 'metaeditor64.exe']:
                                subprocess.run(['taskkill', '/F', '/PID', str(proc.info['pid'])], capture_output=True)
                        except (psutil.NoSuchProcess, psutil.AccessDenied):
                            continue
                    time.sleep(2)  # Give time for processes to terminate
                except Exception as e:
                    self.logger.warning(f"Failed to kill existing MT5 processes: {e}")

                # Create a temporary directory for MT5 data
                temp_dir = tempfile.mkdtemp(prefix="mt5_temp_")
                self.logger.info(f"Created temporary directory for MT5: {temp_dir}")

                # Initialize with retries
                for attempt in range(3):
                    try:
                        initialized = mt5.initialize(
                            path=self.mt5_path,
                            login=self.mt5_login,
                            password=self.mt5_password,
                            server=self.mt5_server,
                            portable=True,
                            timeout=60000,
                            config={
                                "show": False,
                                "autoclose": True,
                                "silent": True
                            }
                        )

                        if initialized:
                            # Verify connection
                            if not mt5.account_info():
                                raise Exception("Failed to get account info after initialization")
                            
                            # Initialize symbols
                            for symbol in self.symbols:
                                if not mt5.symbol_select(symbol, True):
                                    raise Exception(f"Failed to select symbol {symbol}")
                                
                                symbol_info = mt5.symbol_info(symbol)
                                if not symbol_info:
                                    raise Exception(f"Failed to get symbol info for {symbol}")
                                
                                self.point[symbol] = symbol_info.point
                                self.symbol_info[symbol] = {
                                    'digits': symbol_info.digits,
                                    'trade_contract_size': symbol_info.trade_contract_size,
                                    'volume_min': symbol_info.volume_min,
                                    'volume_max': symbol_info.volume_max,
                                    'volume_step': symbol_info.volume_step
                                }
                            
                            self.mt5_connected = True
                            return True

                        error = mt5.last_error()
                        if attempt < 2:
                            self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed: {error}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {attempt + 1} attempts: {error}")
                            return False

                    except Exception as e:
                        if attempt < 2:
                            self.logger.warning(f"MT5 initialization error (attempt {attempt + 1}): {str(e)}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {attempt + 1} attempts with error: {str(e)}")
                            return False

            return False

        except Exception as e:
            self.logger.error(f"Error in ensure_mt5_connection: {str(e)}")
            return False

    def initialize_mt5(self):
        """Initialize MT5 connection and point values for all symbols."""
        # Initialize self.point as a dictionary if not already
        if not hasattr(self, 'point') or not isinstance(self.point, dict):
            self.point = {}
    
        if self.simulate:
            # Initialize point values for simulation mode
            for symbol in self.symbols:
                self.point[symbol] = 0.01 if symbol != "XAUUSD" else 0.01
            self.logger.info("Running in simulation mode; MT5 not initialized.")
            return True
    
        try:
            # First, ensure MT5 is completely shut down
            if mt5.terminal_info():
                mt5.shutdown()
            
            # Force kill any existing MT5 processes
            try:
                import subprocess
                import psutil
                
                # Kill terminal64.exe processes
                for proc in psutil.process_iter(['pid', 'name']):
                    try:
                        if proc.info['name'].lower() in ['terminal64.exe', 'metatrader.exe', 'metaeditor64.exe']:
                            subprocess.run(['taskkill', '/F', '/PID', str(proc.info['pid'])], capture_output=True)
                    except (psutil.NoSuchProcess, psutil.AccessDenied):
                        continue
                
                time.sleep(2)  # Give time for processes to terminate
            except Exception as e:
                self.logger.warning(f"Failed to kill existing MT5 processes: {e}")
    
            # Create a temporary directory for MT5 data
            import tempfile
            import shutil
            temp_dir = tempfile.mkdtemp(prefix="mt5_temp_")
            self.logger.info(f"Created temporary directory for MT5: {temp_dir}")
    
            # Initialize MT5 with retries
            max_retries = 3
            for attempt in range(max_retries):
                try:
                    # Initialize with minimal settings first
                    initialized = mt5.initialize(
                        path=self.mt5_path,
                        login=self.mt5_login,
                        password=self.mt5_password,
                        server=self.mt5_server,
                        portable=True,
                        timeout=60000,
                        config={
                            "show": False,
                            "autoclose": True,
                            "silent": True
                        }
                    )
    
                    if not initialized:
                        error = mt5.last_error()
                        if attempt < max_retries - 1:
                            self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed: {error}. Retrying...")
                            time.sleep(5)
                            continue
                        else:
                            self.logger.error(f"MT5 initialization failed after {max_retries} attempts: {error}")
                            shutil.rmtree(temp_dir, ignore_errors=True)
                            return False
    
                    # Verify connection and login
                    account_info = mt5.account_info()
                    if not account_info:
                        self.logger.error("Failed to get account info")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
                    # Verify trading is enabled
                    terminal = mt5.terminal_info()
                    if not terminal:
                        self.logger.error("Failed to get terminal info")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
                    if not terminal.trade_allowed:
                        self.logger.warning("AutoTrading is disabled, attempting to enable...")
                        # We'll continue anyway as it might be enabled later
    
                    self.logger.info(f"Successfully connected to account {account_info.login} on {self.mt5_server}")
                    self.logger.info(f"Balance: ${account_info.balance:.2f}, Equity: ${account_info.equity:.2f}")
                    self.logger.info(f"Margin Level: {account_info.margin_level:.2f}%")
                    
                    # Initialize symbols
                    for symbol in self.symbols:
                        if not mt5.symbol_select(symbol, True):
                            self.logger.error(f"Failed to select symbol {symbol}")
                            continue
                        
                        symbol_info = mt5.symbol_info(symbol)
                        if symbol_info:
                            # Store point value in dictionary
                            self.point[symbol] = symbol_info.point
                            self.symbol_info[symbol] = {
                                'digits': symbol_info.digits,
                                'trade_contract_size': symbol_info.trade_contract_size,
                                'volume_min': symbol_info.volume_min,
                                'volume_max': symbol_info.volume_max,
                                'volume_step': symbol_info.volume_step
                            }
                            self.logger.info(f"Initialized {symbol}: Point={symbol_info.point}, "
                                           f"Digits={symbol_info.digits}, "
                                           f"Contract Size={symbol_info.trade_contract_size}")
                        else:
                            self.logger.error(f"Failed to get symbol info for {symbol}")
                            self.point[symbol] = 0.01  # Fallback point value
                            continue  # Try to continue with other symbols
    
                    # Validate that all symbols have point values
                    for symbol in self.symbols:
                        if symbol not in self.point:
                            self.logger.warning(f"No point value set for {symbol}, using fallback value 0.01")
                            self.point[symbol] = 0.01
    
                    self.mt5_connected = True
                    return True
    
                except Exception as e:
                    if attempt < max_retries - 1:
                        self.logger.warning(f"MT5 initialization attempt {attempt + 1} failed with error: {str(e)}. Retrying...")
                        time.sleep(5)
                    else:
                        self.logger.error(f"MT5 initialization failed after {max_retries} attempts with error: {str(e)}")
                        shutil.rmtree(temp_dir, ignore_errors=True)
                        return False
    
        except Exception as e:
            self.logger.error(f"Error in initialize_mt5: {str(e)}")
            return False
        finally:
            # Clean up temporary directory if it exists
            try:
                if 'temp_dir' in locals():
                    shutil.rmtree(temp_dir, ignore_errors=True)
            except Exception as e:
                self.logger.warning(f"Failed to clean up temporary directory: {e}")

    def add_account(self, name, login, password, server):
        if name in self.accounts:
            self.logger.warning(f"Account '{name}' already exists.")
            return False
        self.accounts[name] = {"login": int(login), "password": password, "server": server}
        self.logger.info(f"Added account '{name}' with login {login} and server {server}.")
        # If no current account is set, make this the default and initialize
        if not self.current_account:
            self.current_account = name
            self.mt5_login = login
            self.mt5_password = password
            self.mt5_server = server
            if not self.initialize_mt5():
                self.logger.error(f"Failed to initialize MT5 with new account '{name}'.")
                del self.accounts[name]
                return False
        return True

    def load_daily_balance(self):
        """Load daily balance tracking information from file."""
        try:
            if os.path.exists(self.balance_file):
                with open(self.balance_file, 'r') as f:
                    data = json.load(f)
                    # Check if data is from today
                    saved_date = datetime.strptime(data.get('date', ''), '%Y-%m-%d').date()
                    if saved_date == datetime.now().date():
                        self.initial_balance = data.get('initial_balance')
                        self.lowest_balance = data.get('lowest_balance')
                        self.trading_locked = data.get('trading_locked', False)
                        self.trading_lock_reason = data.get('lock_reason', '')
                    else:
                        # New day, get fresh balance
                        self.initialize_daily_balance()
            else:
                self.initialize_daily_balance()
        except Exception as e:
            self.logger.error(f"Error loading daily balance: {str(e)}")
            self.initialize_daily_balance()


    def initialize_daily_balance(self):
        """Initialize daily balance tracking with current MT5 account balance."""
        try:
            if not self.simulate:
                # First ensure MT5 connection
                if not self.ensure_mt5_connection():
                    self.logger.error("Failed to connect to MT5 for balance initialization")
                    return
    
                # Get actual account balance from MT5
                account_info = mt5.account_info()
                if account_info:
                    self.initial_balance = account_info.balance
                    self.lowest_balance = account_info.balance
                    self.trading_locked = False
                    self.trading_lock_reason = ""
                    self.logger.info(f"Initialized daily balance tracking with MT5 balance: ${self.initial_balance:.2f}")
                else:
                    # Log error and exit if can't get balance
                    self.logger.error("Failed to get MT5 account balance")
                    return
            else:
                # For simulation, get actual balance first
                account_info = mt5.account_info()
                if account_info:
                    self.initial_balance = account_info.balance
                else:
                    self.initial_balance = 146.52  # Use current actual balance as fallback
                self.lowest_balance = self.initial_balance
                self.trading_locked = False
                self.trading_lock_reason = ""
    
            self.save_daily_balance()
    
        except Exception as e:
            self.logger.error(f"Error initializing daily balance: {str(e)}")
            # Do not set any default values, just log error and return
            return

    def save_daily_balance(self):
        """Save daily balance tracking information to file."""
        try:
            data = {
                'date': datetime.now().strftime('%Y-%m-%d'),
                'initial_balance': self.initial_balance,
                'lowest_balance': self.lowest_balance,
                'trading_locked': self.trading_locked,
                'lock_reason': self.trading_lock_reason
            }
            with open(self.balance_file, 'w') as f:
                json.dump(data, f)
        except Exception as e:
            self.logger.error(f"Error saving daily balance: {str(e)}")

    def check_drawdown(self):
        """Check if current drawdown exceeds maximum allowed percentage."""
        try:
            if not self.initial_balance:
                return False

            current_balance = 0
            if not self.simulate:
                # Get fresh balance from MT5
                account_info = mt5.account_info()
                if account_info:
                    current_balance = account_info.balance
                else:
                    self.logger.error("Failed to get current MT5 balance")
                    return False
            else:
                # In simulation mode, calculate from tracked profits
                current_balance = self.initial_balance + sum(self.daily_profit.values())

            # Skip drawdown check if initial balance is zero or null
            if not self.initial_balance:
                return False

            # Update lowest balance if current is lower
            if self.lowest_balance is None or current_balance < self.lowest_balance:
                self.lowest_balance = current_balance
                self.save_daily_balance()

            # Calculate drawdown percentage using actual values
            drawdown_percent = ((self.initial_balance - current_balance) / self.initial_balance) * 100 if self.initial_balance > 0 else 0

            if drawdown_percent >= self.max_drawdown_percent:
                message = (
                    f"⚠️ MAXIMUM DRAWDOWN REACHED ⚠️\n"
                    f"Initial Balance: ${self.initial_balance:.2f}\n"
                    f"Current Balance: ${current_balance:.2f}\n"
                    f"Drawdown: {drawdown_percent:.2f}%\n"
                    f"Trading will be locked for the rest of the day."
                )
                self.lock_trading(message)
                self.save_daily_balance()
                return True

            return False

        except Exception as e:
            self.logger.error(f"Error checking drawdown: {str(e)}")
            return False

    def switch_account(self, name):
        if name not in self.accounts:
            self.logger.error(f"Account '{name}' not found.")
            return False
        if name == self.current_account:
            self.logger.info(f"Already on account '{name}'.")
            return True
        
        # Store current positions before switching
        current_positions = {symbol: dict(self.positions[symbol]) for symbol in self.symbols}
        
        # Update current account details
        self.current_account = name
        self.mt5_login = self.accounts[name]["login"]
        self.mt5_password = self.accounts[name]["password"]
        self.mt5_server = self.accounts[name]["server"]
        
        # Reinitialize MT5 with new account
        if not self.initialize_mt5():
            self.logger.error(f"Failed to switch to account '{name}'.")
            return False
        
        # Restore positions or sync with new account
        self.positions = {symbol: {} for symbol in self.symbols}  # Reset positions
        self.sync_positions_with_mt5()
        
        self.logger.info(f"Switched to account '{name}' successfully.")
        return True

    def sync_positions_with_mt5(self):
        """Enhanced synchronization with MT5 including proper script trade tracking."""
        if self.simulate:
            return True

        try:
            # Get all current MT5 positions
            mt5_positions = mt5.positions_get()
            if mt5_positions is None:
                self.logger.error("Failed to get positions from MT5")
                return False
                
            mt5_tickets = {pos.ticket for pos in mt5_positions}
            
            # Use a timeout context for the lock
            if not self.command_lock.acquire(timeout=5):
                self.logger.error("Failed to acquire lock for position synchronization")
                return False
                
            try:
                for symbol in self.symbols:
                    # Check for positions that exist in our tracking but not in MT5
                    for ticket in list(self.positions[symbol].keys()):
                        if ticket not in mt5_tickets:
                            # Position was closed externally
                            position = self.positions[symbol][ticket]
                            self.logger.info(f"[{symbol}] Position {ticket} closed externally, updating records")
                            
                            # Calculate final profit if possible
                            profit_points = 0
                            if mt5_positions:
                                for mt5_pos in mt5_positions:
                                    if mt5_pos.ticket == ticket:
                                        profit_points = self.convert_to_points(mt5_pos.profit, symbol)
                                        break
                            
                            # Update trade history
                            self.update_trade_history_on_close(ticket, symbol, profit_points, "Closed externally")
                            
                            # Remove from tracking
                            del self.positions[symbol][ticket]
                    
                    # Add any new positions from MT5 that we're not tracking
                    for pos in mt5_positions:
                        if pos.symbol == symbol and pos.ticket not in self.positions[symbol]:
                            # Check if this is a script-placed trade based on comment
                            is_script_trade = pos.comment and pos.comment.startswith("GC_Signals_")
                            strategy = pos.comment.replace("GC_Signals_", "") if is_script_trade else "external"
                            
                            if not is_script_trade:
                                # This is an external trade - add it with external trade handling
                                self.handle_external_trade(pos)
                            else:
                                # This is our trade that somehow got disconnected - restore it
                                self.positions[symbol][pos.ticket] = {
                                    'ticket': pos.ticket,
                                    'type': pos.type,
                                    'entry_price': pos.price_open,
                                    'lot_size': pos.volume,
                                    'sl': pos.sl,
                                    'tp': pos.tp,
                                    'timeframe': mt5.TIMEFRAME_M1,  # Default to M1 if unknown
                                    'strategy': strategy,
                                    'entry_time': datetime.fromtimestamp(pos.time).strftime('%Y-%m-%d %H:%M:%S.%f'),
                                    'signal_time': datetime.fromtimestamp(pos.time).strftime('%Y-%m-%d %H:%M:%S.%f'),
                                    'breakeven_triggered': False,
                                    'trailing_active': False,
                                    'thread_id': None,
                                    'reason': strategy,
                                    'comments': pos.comment,
                                    'symbol': symbol,
                                    'profit': pos.profit,
                                    'script_placed': True
                                }
                                self.logger.info(f"[{symbol}] Restored script-placed trade {pos.ticket}")
            finally:
                self.command_lock.release()
            
            self.save_trade_history()
            return True
            
        except Exception as e:
            self.logger.error(f"Error in sync_positions_with_mt5: {str(e)}")
            if self.command_lock.locked():
                self.command_lock.release()
            return False

    def prompt_position_params(self, position):
        """Prompt for position parameters after trade entry."""
        symbol = position['symbol']
        point = self.point[symbol]  # Get point value directly from self.point dictionary
        
        # Calculate current parameters in points
        current_sl_points = abs(position['sl'] - position['entry_price']) / point if position['sl'] else 0
        current_tp_points = abs(position['tp'] - position['entry_price']) / point if position['tp'] else 0
        
        message = (
            f"🔧 Position Parameters Required:\n"
            f"Ticket: {position['ticket']}\n"
            f"Symbol: {symbol}\n"
            f"Entry: {position['entry_price']:.5f}\n"
            f"Current Settings:\n"
            f"- SL: {current_sl_points:.0f} points\n"
            f"- TP: {current_tp_points:.0f} points\n"
            f"- Trail Stop: {self.trailing_stop_configs[position['timeframe']]:.1f} points\n"
            f"- Trail Delay: {self.trailing_delay_configs[position['timeframe']]:.1f} points\n"
            f"- MA Exit: {'Enabled' if self.ma_exit_enabled[symbol][position['timeframe']] else 'Disabled'}\n\n"
            f"Reply with: setparams <ticket> <sl_points> <tp_points> <trail_stop> <trail_delay> <ma_exit>\n"
            f"Example: setparams {position['ticket']} 100 200 20 50 1\n"
            f"(Use 0 for default values, 1/0 for ma_exit enable/disable)"
        )
        
        # Send to both interfaces
        self.send_telegram_message(message)
        print(f"\n{message}")
        position['waiting_params'] = True

    def handle_position_params(self, cmd_parts):
        """Handle the setparams command for position parameters."""
        try:
            if len(cmd_parts) != 7:
                return "Invalid parameters. Usage: setparams <ticket> <sl_points> <tp_points> <trail_stop> <trail_delay> <ma_exit>"
            
            _, ticket, sl_points, tp_points, trail_stop, trail_delay, ma_exit = cmd_parts
            ticket = int(ticket)
            
            # Find position
            position = None
            symbol = None
            for sym in self.symbols:
                if ticket in self.positions[sym]:
                    position = self.positions[sym][ticket]
                    symbol = sym
                    break
            
            if not position:
                return f"Position with ticket {ticket} not found."
            
            if not position.get('waiting_params', False):
                return f"Position {ticket} is not waiting for parameter settings."
            
            # Get symbol point value
            point = self.point[symbol]
            
            # Calculate actual SL/TP prices based on points
            sl_points = float(sl_points)
            tp_points = float(tp_points)
            
            if sl_points > 0:
                sl = (position['entry_price'] - sl_points * point) if position['type'] == mt5.ORDER_TYPE_BUY else \
                    (position['entry_price'] + sl_points * point)
            else:
                sl = position['sl']
                
            if tp_points > 0:
                tp = (position['entry_price'] + tp_points * point) if position['type'] == mt5.ORDER_TYPE_BUY else \
                    (position['entry_price'] - tp_points * point)
            else:
                tp = position['tp']
            
            trail_stop = float(trail_stop) if float(trail_stop) != 0 else self.trailing_stop_configs[position['timeframe']]
            trail_delay = float(trail_delay) if float(trail_delay) != 0 else self.trailing_delay_configs[position['timeframe']]
            ma_exit = bool(int(ma_exit))
            
            # Apply parameters
            success = self.modify_position(position, sl=sl, tp=tp)
            if not success:
                return "Failed to modify position parameters"
                
            self.trailing_stop_configs[position['timeframe']] = trail_stop
            self.trailing_delay_configs[position['timeframe']] = trail_delay
            self.ma_exit_enabled[symbol][position['timeframe']] = ma_exit
            
            position['waiting_params'] = False
            
            return (f"Parameters set for ticket {ticket}:\n"
                    f"SL: {sl_points:.0f} points (Price: {sl:.5f})\n"
                    f"TP: {tp_points:.0f} points (Price: {tp:.5f})\n"
                    f"Trail Stop: {trail_stop} points\n"
                    f"Trail Delay: {trail_delay} points\n"
                    f"MA Exit: {'Enabled' if ma_exit else 'Disabled'}")
                    
        except Exception as e:
            return f"Error setting parameters: {str(e)}"

    def generate_trade_report(self, ticket=None, symbol=None, daily=False):
        """Generate detailed trade report in PDF format with embedded charts including Parabolic SAR and MACD using TA-Lib."""
        try:
            # Create PDF document
            filename = f"trade_report_{datetime.now().strftime('%Y%m%d_%H%M%S')}.pdf"
            filepath = os.path.join(self.reports_folder, filename)
            
            doc = SimpleDocTemplate(filepath, pagesize=letter)
            story = []
            
            # Get trades to report
            trades = []
            title = ""
            if ticket:
                # For ticket-specific report
                title = f"TRADE REPORT TICKET No. {ticket}"
                for sym in self.symbols:
                    # Check current open positions
                    if ticket in self.positions[sym]:
                        position = self.positions[sym][ticket]
                        trade = {
                            'ticket': position['ticket'],
                            'type': "BUY" if position['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                            'entry_price': position['entry_price'],
                            'close_price': None,
                            'sl': position['sl'],
                            'tp': position['tp'],
                            'lot_size': position['lot_size'],
                            'entry_time': position['entry_time'],
                            'close_time': None,
                            'symbol': sym,
                            'timeframe': position['timeframe'],
                            'profit': position['profit'],
                            'reason': position.get('reason', 'Manual/External Trade'),
                            'comments': position.get('comments', ''),
                            'status': 'open'
                        }
                        trades.append(trade)
                    
                    # Check all history categories
                    for history_list in [
                        self.trade_history[sym],
                        self.grid_history[sym],
                        self.suretrend_history[sym],
                        self.momentum_history[sym]
                    ]:
                        trades.extend([t for t in history_list if t.get('ticket') == ticket])
                    
                    # Get MT5 history for the ticket
                    if not self.simulate:
                        mt5_history = mt5.history_deals_get(ticket=ticket)
                        if mt5_history:
                            for deal in mt5_history:
                                if not any(t.get('ticket') == deal.ticket for t in trades):
                                    trades.append({
                                        'ticket': deal.ticket,
                                        'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                        'entry_price': deal.price,
                                        'close_price': deal.price,
                                        'sl': 0.0,
                                        'tp': 0.0,
                                        'lot_size': deal.volume,
                                        'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'symbol': deal.symbol,
                                        'timeframe': 'M1',
                                        'profit': deal.profit,
                                        'reason': 'External MT5 Trade',
                                        'comments': deal.comment,
                                        'status': 'closed'
                                    })
                    
            elif symbol:
                # For symbol-specific report
                title = f"TRADE REPORT {symbol}"
                # Include current open positions
                for pos in self.positions[symbol].values():
                    trades.append({
                        'ticket': pos['ticket'],
                        'type': "BUY" if pos['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                        'entry_price': pos['entry_price'],
                        'close_price': None,
                        'sl': pos['sl'],
                        'tp': pos['tp'],
                        'lot_size': pos['lot_size'],
                        'entry_time': pos['entry_time'],
                        'close_time': None,
                        'symbol': symbol,
                        'timeframe': pos['timeframe'],
                        'profit': pos['profit'],
                        'reason': pos.get('reason', 'Manual/External Trade'),
                        'comments': pos.get('comments', ''),
                        'status': 'open'
                    })
                
                # Add all historical trades
                trades.extend(self.trade_history[symbol])
                trades.extend(self.grid_history[symbol])
                trades.extend(self.suretrend_history[symbol])
                trades.extend(self.momentum_history[symbol])
                
                # Get MT5 history for the symbol
                if not self.simulate:
                    mt5_history = mt5.history_deals_get(
                        datetime.now() - timedelta(days=7),
                        datetime.now(),
                        symbol=symbol
                    )
                    if mt5_history:
                        for deal in mt5_history:
                            if not any(t.get('ticket') == deal.ticket for t in trades):
                                trades.append({
                                    'ticket': deal.ticket,
                                    'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                    'entry_price': deal.price,
                                    'close_price': deal.price,
                                    'sl': 0.0,
                                    'tp': 0.0,
                                    'lot_size': deal.volume,
                                    'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                    'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                    'symbol': symbol,
                                    'timeframe': 'M1',
                                    'profit': deal.profit,
                                    'reason': 'External MT5 Trade',
                                    'comments': deal.comment,
                                    'status': 'closed'
                                })
                    
            elif daily:
                # For daily report
                title = f"DAILY TRADE REPORT {datetime.now().strftime('%Y-%m-%d')}"
                today = datetime.now().date()
                
                for sym in self.symbols:
                    # Include current open positions opened today
                    for pos in self.positions[sym].values():
                        if self.parse_trade_time(pos['entry_time']).date() == today:
                            trades.append({
                                'ticket': pos['ticket'],
                                'type': "BUY" if pos['type'] == mt5.ORDER_TYPE_BUY else "SELL",
                                'entry_price': pos['entry_price'],
                                'close_price': None,
                                'sl': pos['sl'],
                                'tp': pos['tp'],
                                'lot_size': pos['lot_size'],
                                'entry_time': pos['entry_time'],
                                'close_time': None,
                                'symbol': sym,
                                'timeframe': pos['timeframe'],
                                'profit': pos['profit'],
                                'reason': pos.get('reason', 'Manual/External Trade'),
                                'comments': pos.get('comments', ''),
                                'status': 'open'
                            })
                    
                    # Add all historical trades from today
                    for history_list in [
                        self.trade_history[sym],
                        self.grid_history[sym],
                        self.suretrend_history[sym],
                        self.momentum_history[sym]
                    ]:
                        trades.extend([t for t in history_list 
                                     if self.parse_trade_time(t.get('entry_time', '')).date() == today])
                    
                    # Get today's MT5 history
                    if not self.simulate:
                        today_start = datetime.combine(today, datetime.min.time())
                        mt5_history = mt5.history_deals_get(today_start, datetime.now(), symbol=sym)
                        if mt5_history:
                            for deal in mt5_history:
                                if not any(t.get('ticket') == deal.ticket for t in trades):
                                    trades.append({
                                        'ticket': deal.ticket,
                                        'type': "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                                        'entry_price': deal.price,
                                        'close_price': deal.price,
                                        'sl': 0.0,
                                        'tp': 0.0,
                                        'lot_size': deal.volume,
                                        'entry_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'close_time': datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                                        'symbol': sym,
                                        'timeframe': 'M1',
                                        'profit': deal.profit,
                                        'reason': 'External MT5 Trade',
                                        'comments': deal.comment,
                                        'status': 'closed'
                                    })
            
            if not trades:
                return "No trades found for the specified criteria."
        
            # Add title
            story.append(Paragraph(title, ParagraphStyle('Title', fontSize=14, spaceAfter=20)))
            
            # Process trades
            for trade in trades:
                try:
                    # Get timeframe (handle both string and numeric formats)
                    trade_tf = trade.get('timeframe')
                    if isinstance(trade_tf, str):
                        timeframe = self.parse_timeframe(trade_tf)
                        tf_name = trade_tf
                    else:
                        timeframe = trade_tf
                        tf_name = self.get_timeframe_name(trade_tf)
                    
                    if not timeframe:
                        # If timeframe is invalid or missing, try to determine from trade history
                        time_diff = None
                        if trade.get('entry_time') and trade.get('close_time'):
                            entry = self.parse_trade_time(trade['entry_time'])
                            close = self.parse_trade_time(trade['close_time'])
                            time_diff = (close - entry).total_seconds()
                        
                        # Assign appropriate timeframe based on trade duration
                        if time_diff:
                            if time_diff <= 3600:  # 1 hour or less
                                timeframe = mt5.TIMEFRAME_M5
                                tf_name = 'M5'
                            elif time_diff <= 14400:  # 4 hours or less
                                timeframe = mt5.TIMEFRAME_M15
                                tf_name = 'M15'
                            else:
                                timeframe = mt5.TIMEFRAME_H1
                                tf_name = 'H1'
                        else:
                            # Default to M5 if can't determine
                            timeframe = mt5.TIMEFRAME_M5
                            tf_name = 'M5'
                    
                    # Trade placed details
                    trade_type = "Buy" if trade.get('type') == "BUY" else "Sell"
                    entry_details = (
                        f"Trade Placed: {trade_type} {trade.get('symbol', '')} {tf_name} "
                        f"Ticket no{trade.get('ticket', '')} placed {trade.get('entry_price', 0.0):.5f} "
                        f"due to {trade.get('reason', 'N/A')}"
                    )
                    story.append(Paragraph(entry_details, ParagraphStyle('Normal', spaceBefore=10)))
                    
                    # Add chart for the trade
                    symbol = trade.get('symbol')
                    entry_time = self.parse_trade_time(trade.get('entry_time', ''))
                    
                    # Get historical data around the trade time with appropriate timeframe
                    df = self.get_rates(symbol, timeframe=timeframe)
                    if df is not None:
                        df = self.calculate_indicators(df, timeframe, symbol)
                        
                        # Calculate Parabolic SAR and MACD using TA-Lib
                        import talib
                        import numpy as np
                        
                        # Ensure sufficient data for indicators
                        if len(df) < 26:  # Minimum for MACD slow EMA
                            self.logger.warning(f"Insufficient data for indicators on {symbol} {tf_name}: {len(df)} rows")
                            story.append(Paragraph(f"Insufficient data for indicators for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Convert to NumPy arrays for TA-Lib
                        high = np.array(df['high'], dtype=float)
                        low = np.array(df['low'], dtype=float)
                        close = np.array(df['close'], dtype=float)
                        
                        # Parabolic SAR
                        df['sar'] = talib.SAR(high, low, acceleration=0.02, maximum=0.2)
                        
                        # MACD
                        macd, macd_signal, macd_hist = talib.MACD(
                            close,
                            fastperiod=12,
                            slowperiod=26,
                            signalperiod=9
                        )
                        df['macd'] = macd
                        df['macd_signal'] = macd_signal
                        df['macd_hist'] = macd_hist
                        
                        # Create figure with subplots (main chart + MACD)
                        from plotly.subplots import make_subplots
                        fig = make_subplots(
                            rows=2, cols=1,
                            row_heights=[0.7, 0.3],
                            shared_xaxes=True,
                            vertical_spacing=0.1,
                            subplot_titles=[f"{symbol} {tf_name} Trade Chart", "MACD"]
                        )
                        
                        # Add candlestick chart to main plot (row 1)
                        fig.add_trace(
                            go.Candlestick(
                                x=df['time'],
                                open=df['open'],
                                high=df['high'],
                                low=df['low'],
                                close=df['close'],
                                name='OHLC'
                            ),
                            row=1, col=1
                        )
                        
                        # Add moving averages to main plot
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['ma_fast'],
                                mode='lines',
                                name=f'MA {self.ma_configs[timeframe]["fast"]}',
                                line=dict(color='blue')
                            ),
                            row=1, col=1
                        )
                        
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['ma_slow'],
                                mode='lines',
                                name=f'MA {self.ma_configs[timeframe]["slow"]}',
                                line=dict(color='red')
                            ),
                            row=1, col=1
                        )
                        
                        # Add Parabolic SAR to main plot
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['sar'],
                                mode='markers',
                                name='Parabolic SAR',
                                marker=dict(symbol='circle', size=5, color='purple')
                            ),
                            row=1, col=1
                        )
                        
                        # Add entry and exit points to main plot
                        entry_price = trade.get('entry_price')
                        exit_price = trade.get('close_price')
                        
                        fig.add_hline(y=entry_price, line_dash="dash", line_color="blue", annotation_text="Entry", row=1)
                        if exit_price:
                            fig.add_hline(y=exit_price, line_dash="dash", line_color="red", annotation_text="Exit", row=1)
                        
                        # Add SL/TP lines if available to main plot
                        if trade.get('sl'):
                            fig.add_hline(y=trade['sl'], line_dash="dot", line_color="red", annotation_text="SL", row=1)
                        if trade.get('tp'):
                            fig.add_hline(y=trade['tp'], line_dash="dot", line_color="green", annotation_text="TP", row=1)
                        
                        # Add MACD to subplot (row 2)
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['macd'],
                                mode='lines',
                                name='MACD',
                                line=dict(color='blue')
                            ),
                            row=2, col=1
                        )
                        
                        fig.add_trace(
                            go.Scatter(
                                x=df['time'],
                                y=df['macd_signal'],
                                mode='lines',
                                name='Signal',
                                line=dict(color='orange')
                            ),
                            row=2, col=1
                        )
                        
                        fig.add_trace(
                            go.Bar(
                                x=df['time'],
                                y=df['macd_hist'],
                                name='Histogram',
                                marker_color=df['macd_hist'].apply(lambda x: 'green' if x >= 0 else 'red')
                            ),
                            row=2, col=1
                        )
                        
                        # Add profit annotation to main plot
                        if trade.get('profit_points'):
                            fig.add_annotation(
                                x=df['time'].iloc[-1],
                                y=exit_price or df['close'].iloc[-1],
                                text=f"Profit: {trade.get('profit_points', 0):.2f} points",
                                showarrow=True,
                                arrowhead=1,
                                row=1, col=1
                            )
                        
                        # Update layout
                        fig.update_layout(
                            height=500,
                            margin=dict(l=50, r=50, t=50, b=50),
                            showlegend=True,
                            xaxis2=dict(title='Time'),
                            yaxis=dict(title='Price'),
                            yaxis2=dict(title='MACD')
                        )
                        
                        # Save chart as temporary image with absolute path
                        temp_chart = os.path.join(self.reports_folder, f"temp_chart_{trade.get('ticket')}.png")
                        try:
                            self.logger.debug(f"Attempting to write chart to {temp_chart}")
                            fig.write_image(temp_chart, engine="kaleido")
                            self.logger.debug(f"Chart written to {temp_chart}")
                        except Exception as e:
                            self.logger.error(f"Failed to write chart image {temp_chart}: {str(e)}")
                            story.append(Paragraph(f"Chart generation failed for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Verify file exists before adding to PDF
                        if not os.path.exists(temp_chart):
                            self.logger.error(f"Chart image {temp_chart} was not created.")
                            story.append(Paragraph(f"Chart missing for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Add chart to PDF
                        try:
                            img = Image(temp_chart)
                            img.drawHeight = 350
                            img.drawWidth = 500
                            story.append(img)
                            story.append(Spacer(1, 20))
                        except Exception as e:
                            self.logger.error(f"Failed to add chart {temp_chart} to PDF: {str(e)}")
                            story.append(Paragraph(f"Chart inclusion failed for ticket {trade.get('ticket')}.", 
                                                 ParagraphStyle('Normal')))
                            continue
                        
                        # Clean up temporary file
                        try:
                            os.remove(temp_chart)
                            self.logger.debug(f"Deleted temporary chart {temp_chart}")
                        except Exception as e:
                            self.logger.warning(f"Failed to delete temporary chart {temp_chart}: {str(e)}")
                    
                    # Add SL/TP details
                    sl_tp_details = (
                        f"Initial SL: {trade.get('sl', 'N/A'):.5f}, "
                        f"TP: {trade.get('tp', 'N/A'):.5f}"
                    )
                    story.append(Paragraph(sl_tp_details, ParagraphStyle('Normal', leftIndent=20)))
                    
                    # Add close details if trade is closed
                    if trade.get('close_time'):
                        close_details = (
                            f"Trade Closed: The trade {trade_type} {trade.get('symbol', '')} {tf_name} "
                            f"Ticket no{trade.get('ticket', '')} was closed at {trade.get('close_time', '')} "
                            f"due to {trade.get('close_reason', 'N/A')}"
                        )
                        story.append(Paragraph(close_details, ParagraphStyle('Normal', spaceBefore=10)))
                    
                    story.append(Spacer(1, 20))
                    
                except Exception as e:
                    self.logger.error(f"Error processing trade {trade.get('ticket', 'unknown')}: {str(e)}")
                    continue
            
            # Build PDF
            doc.build(story)
            
            # Send report via Telegram if available
            if self.TELEGRAM_BOT_TOKEN and self.TELEGRAM_CHAT_ID:
                try:
                    with open(filepath, 'rb') as f:
                        url = f"https://api.telegram.org/bot{self.TELEGRAM_BOT_TOKEN}/sendDocument"
                        files = {'document': f}
                        data = {'chat_id': self.TELEGRAM_CHAT_ID}
                        response = requests.post(url, data=data, files=files)
                        if not response.json().get('ok'):
                            self.logger.error(f"Failed to send report via Telegram: {response.json()}")
                except Exception as e:
                    self.logger.error(f"Error sending report via Telegram: {str(e)}")
            
            return f"Report generated successfully: {filepath}"
            
        except Exception as e:
            self.logger.error(f"Error generating trade report: {str(e)}")
            return f"Failed to generate report: {str(e)}"
    
    def parse_trade_time(self, time_str):
        """Parse trade time string handling both formats with and without microseconds."""
        try:
            # Try parsing with microseconds
            return datetime.strptime(time_str, '%Y-%m-%d %H:%M:%S.%f')
        except ValueError:
            try:
                # Try parsing without microseconds
                return datetime.strptime(time_str, '%Y-%m-%d %H:%M:%S')
            except ValueError:
                # Return current time if parsing fails
                self.logger.error(f"Failed to parse time string: {time_str}")
                return datetime.now()

    def convert_to_points(self, profit, symbol):
        """Enhanced conversion of profit to points with proper null handling."""
        try:
            if profit is None or self.point.get(symbol) is None:
                return 0.0
            
            # Get lot size from position if available, otherwise use default
            lot_size = getattr(self, 'lot_size', 0.1)  # Default to 0.1 if not set
            point_value = self.point[symbol] * lot_size * 10000
            
            # Avoid division by zero
            if point_value == 0:
                return 0.0
            
            return profit / point_value
        except Exception as e:
            self.logger.debug(f"Error converting profit to points: {str(e)}")
            return 0.0

    def update_trade_history_on_close(self, ticket, symbol, profit_points, reason):
        """Enhanced trade history update with better error handling"""
        try:
            with self.command_lock:
                close_time = datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f')
                
                # Safely calculate actual profit
                try:
                    point_value = self.point.get(symbol, 0.0)
                    lot_size = getattr(self, 'lot_size', 0.1)
                    actual_profit = profit_points * point_value * lot_size * 10000 if all(v is not None for v in [profit_points, point_value, lot_size]) else 0.0
                except Exception as e:
                    self.logger.debug(f"Error calculating actual profit: {str(e)}")
                    actual_profit = 0.0
                
                # Update profit and close time in all history lists
                for history in [self.trade_history, self.grid_history, self.suretrend_history, self.momentum_history]:
                    if symbol in history:
                        for trade in history[symbol]:
                            try:
                                if trade.get('ticket') == ticket:
                                    trade['profit'] = actual_profit
                                    trade['profit_points'] = profit_points
                                    trade['close_time'] = close_time
                                    trade['close_reason'] = reason
                                    trade['status'] = 'closed'
                                    break
                            except Exception as e:
                                self.logger.debug(f"Error updating trade {ticket}: {str(e)}")
                            continue
                
                self.save_trade_history()
                
        except Exception as e:
            self.logger.error(f"Error updating trade history on close: {str(e)}")

    def get_rates(self, symbol, num_candles=100, timeframe=None):
        """Enhanced rate retrieval with better error handling"""
        if self.simulate:
            return self.get_simulated_rates(symbol, num_candles, timeframe)
        
        retry_count = 0
        while retry_count < self.max_retries:
            try:
                # First ensure MT5 is initialized
                if not self.ensure_mt5_connection():
                    raise Exception("Failed to ensure MT5 connection")
                
                # Convert string timeframe to MT5 timeframe constant if needed
                if isinstance(timeframe, str):
                    timeframe = self.timeframe_configs.get(timeframe.upper())
                    if timeframe is None:
                        raise Exception(f"Invalid timeframe string: {timeframe}")
                
                # Verify timeframe is valid
                valid_timeframes = [mt5.TIMEFRAME_M1, mt5.TIMEFRAME_M5, mt5.TIMEFRAME_M15, 
                                  mt5.TIMEFRAME_M30, mt5.TIMEFRAME_H1, mt5.TIMEFRAME_H4]
                if timeframe not in valid_timeframes:
                    raise Exception(f"Invalid timeframe value: {timeframe}")
                
                # Get rates with explicit error checking
                rates = mt5.copy_rates_from_pos(symbol, timeframe, 0, max(num_candles, 100))  # Always get at least 100 candles
                if rates is None:
                    error = mt5.last_error()
                    raise Exception(f"copy_rates_from_pos failed: {error}")
                
                if len(rates) == 0:
                    raise Exception("No rates returned")
                
                # Convert to DataFrame
                df = pd.DataFrame(rates)
                df['time'] = pd.to_datetime(df['time'], unit='s')
                
                # Cache the data
                if symbol in self.data_cache and timeframe in self.data_cache[symbol]:
                    self.data_cache[symbol][timeframe]['df'] = df
                    self.data_cache[symbol][timeframe]['last_time'] = df['time'].iloc[-1]
                
                self.logger.debug(f"[{symbol}] Successfully retrieved {len(df)} candles for {self.get_timeframe_name(timeframe)}")
                return df
                
            except Exception as e:
                retry_count += 1
                self.logger.error(f"[{symbol}] Failed to get rates (attempt {retry_count}/{self.max_retries}): {str(e)}")
                
                if retry_count < self.max_retries:
                    sleep_time = min(300, self.retry_delay * (2 ** (retry_count - 1)) + random.uniform(0, 1))
                    self.logger.info(f"[{symbol}] Waiting {sleep_time:.1f} seconds before retry...")
                    time.sleep(sleep_time)
                    
                    # Try to use cached data if available
                    if symbol in self.data_cache and timeframe in self.data_cache[symbol]:
                        cached_df = self.data_cache[symbol][timeframe]['df']
                        if cached_df is not None and len(cached_df) > 0:
                            self.logger.warning(f"[{symbol}] Using cached data due to rate retrieval failure")
                            return cached_df
                else:
                    self.logger.error(f"[{symbol}] Failed to get rates after {self.max_retries} attempts")
                    # Try one last time to use cached data
                    if symbol in self.data_cache and timeframe in self.data_cache[symbol]:
                        cached_df = self.data_cache[symbol][timeframe]['df']
                        if cached_df is not None and len(cached_df) > 0:
                            self.logger.warning(f"[{symbol}] Using cached data as final fallback")
                            return cached_df
        
        return None

    def save_lock_state(self):
        """Save trading lock state to file."""
        try:
            lock_data = {
                'locked': self.trading_locked,
                'reason': self.trading_lock_reason,
                'date': datetime.now().strftime('%Y-%m-%d')
            }
            with open(self.lock_file, 'w') as f:
                json.dump(lock_data, f)
        except Exception as e:
            self.logger.error(f"Error saving lock state: {str(e)}")

    def load_lock_state(self):
        """Load trading lock state from file."""
        try:
            if os.path.exists(self.lock_file):
                with open(self.lock_file, 'r') as f:
                    lock_data = json.load(f)
                    # Check if lock is from today
                    lock_date = datetime.strptime(lock_data.get('date', ''), '%Y-%m-%d').date()
                    if lock_date == datetime.now().date():
                        self.trading_locked = lock_data.get('locked', False)
                        self.trading_lock_reason = lock_data.get('reason', '')
                        if self.trading_locked:
                            self.logger.warning(f"Loaded trading lock: {self.trading_lock_reason}")
                    else:
                        # Reset lock if it's from a previous day
                        self.trading_locked = False
                        self.trading_lock_reason = ""
                        self.save_lock_state()
        except Exception as e:
            self.logger.error(f"Error loading lock state: {str(e)}")
            self.trading_locked = False
            self.trading_lock_reason = ""

    def lock_trading(self, reason):
        """Lock all trading with a specific reason."""
        self.trading_locked = True
        self.trading_lock_reason = reason
        
        # Save lock state to file
        self.save_lock_state()
        
        # Close all open positions
        for symbol in self.symbols:
            for position in list(self.positions[symbol].values()):
                self.close_position(position, "Trading locked: " + reason)
        
        # Log and notify with enhanced message
        message = (
            f"🔒 TRADING LOCKED\n"
            f"Reason: {reason}\n"
            f"⚠️ Trading will remain locked until unlocked by team leader.\n"
            f"📞 Contact your team leader for authorization to resume trading."
        )
        self.logger.warning(message)
        self.send_telegram_message(message)

    def unlock_trading(self, password):
        """Attempt to unlock trading with admin password."""
        if password != self.ADMIN_PASSWORD:
            self.logger.warning("Invalid password attempt to unlock trading")
            return "Invalid password. Contact team leader for assistance."
        
        self.trading_locked = False
        self.trading_lock_reason = ""
        
        # Save unlocked state to file
        self.save_lock_state()
        
        # Reset daily profit/loss tracking
        for symbol in self.symbols:
            self.daily_profit[symbol] = 0.0
        
        message = "🔓 Trading unlocked by administrator. Daily profit/loss counters reset."
        self.logger.info(message)
        self.send_telegram_message(message)
        return message

    def get_or_update_rates(self, symbol, timeframe):
        try:
            # Convert string timeframe to MT5 constant if needed
            if isinstance(timeframe, str):
                timeframe = self.timeframe_configs.get(timeframe.upper())
                if timeframe is None:
                    raise ValueError(f"Invalid timeframe string: {timeframe}")

            # Get current rates
            current_rates = self.get_rates(symbol, 100, timeframe)
            if current_rates is None:
                self.logger.error(f"[{symbol}] Failed to get rates for {self.get_timeframe_name(timeframe)}")
                return None

            current_time = current_rates['time'].iloc[-1]
            
            # Initialize cache if needed
            if symbol not in self.data_cache:
                self.data_cache[symbol] = {}
            if timeframe not in self.data_cache[symbol]:
                self.data_cache[symbol][timeframe] = {'df': None, 'last_time': None}
                
            cache = self.data_cache[symbol][timeframe]
            
            # Always calculate indicators for fresh data
            calculated_df = self.calculate_indicators(current_rates, timeframe, symbol)
            if calculated_df is None:
                self.logger.error(f"[{symbol}] Failed to calculate indicators for {self.get_timeframe_name(timeframe)}")
                # Try to use cached data if available
                if cache['df'] is not None and len(cache['df']) > 0:
                    self.logger.warning(f"[{symbol}] Using cached data due to calculation failure")
                    return cache['df']
                return None
                
            # Verify all required columns are present
            required_columns = ['ma_crossover', 'momentum', 'close', 'psar', 'macd_crossover', 'bb_expanding']
            missing_columns = [col for col in required_columns if col not in calculated_df.columns]
            
            if missing_columns:
                self.logger.error(f"[{symbol}] Missing columns after calculation: {missing_columns}")
                if cache['df'] is not None and len(cache['df']) > 0:
                    self.logger.warning(f"[{symbol}] Using cached data due to missing columns")
                    return cache['df']
                return None
                
            # Update cache with new data
            cache['df'] = calculated_df
            cache['last_time'] = current_time
            
            return calculated_df
            
        except Exception as e:
            self.logger.error(f"[{symbol}] Error in get_or_update_rates: {str(e)}")
            if symbol in self.data_cache and timeframe in self.data_cache[symbol]:
                cache = self.data_cache[symbol][timeframe]
                if cache['df'] is not None and len(cache['df']) > 0:
                    self.logger.warning(f"[{symbol}] Using cached data due to error")
                    return cache['df']
            return None

    def calculate_indicators(self, df, timeframe, symbol):
        try:
            if df is None or len(df) < 26:  # Need at least 26 bars for MACD calculation
                self.logger.error(f"[{symbol}] Insufficient data for indicator calculation (need at least 26 bars)")
                return None
                
            # Ensure we have the required OHLC columns
            required_ohlc = ['open', 'high', 'low', 'close']
            if not all(col in df.columns for col in required_ohlc):
                self.logger.error(f"[{symbol}] Missing required OHLC columns")
                return None
                
            try:
                # Calculate moving averages first
                ma_fast_period = max(3, self.ma_configs[timeframe]['fast'])
                ma_slow_period = max(5, self.ma_configs[timeframe]['slow'])
                exit_fast = max(3, self.ma_configs[timeframe]['exit_fast'])
                exit_slow = max(5, self.ma_configs[timeframe]['exit_slow'])
                
                # Calculate basic MAs
                df['ma_fast'] = talib.SMA(df['close'], timeperiod=ma_fast_period)
                df['ma_slow'] = talib.SMA(df['close'], timeperiod=ma_slow_period)
                df['exit_ma_fast'] = talib.SMA(df['close'], timeperiod=exit_fast)
                df['exit_ma_slow'] = talib.SMA(df['close'], timeperiod=exit_slow)
                
                # Calculate MA crossovers
                df['ma_crossover'] = (df['ma_fast'] > df['ma_slow']) & (df['ma_fast'].shift(1) <= df['ma_slow'].shift(1))
                df['ma_crossunder'] = (df['ma_fast'] < df['ma_slow']) & (df['ma_fast'].shift(1) >= df['ma_slow'].shift(1))
                
                # Calculate momentum with minimum period of 5
                momentum_period = max(5, self.momentum_period)
                df['momentum'] = talib.MOM(df['close'], timeperiod=momentum_period)
                
                # Add RSI
                rsi_period = max(5, self.rsi_period)
                df['rsi'] = talib.RSI(df['close'], timeperiod=rsi_period)
                
                # Calculate PSAR with safe parameters
                df['psar'] = talib.SAR(df['high'], df['low'], acceleration=max(0.02, self.psar_step), maximum=max(0.2, self.psar_max))
                
                # Calculate MACD with minimum periods
                macd_fast = max(5, self.macd_fast)
                macd_slow = max(13, self.macd_slow)
                macd_signal = max(5, self.macd_signal)
                df['macd'], df['macd_signal'], _ = talib.MACD(
                    df['close'], 
                    fastperiod=macd_fast, 
                    slowperiod=macd_slow, 
                    signalperiod=macd_signal
                )
                
                # Calculate MACD crossovers
                df['macd_crossover'] = (df['macd'] > df['macd_signal']) & (df['macd'].shift(1) <= df['macd_signal'].shift(1))
                df['macd_crossunder'] = (df['macd'] < df['macd_signal']) & (df['macd'].shift(1) >= df['macd_signal'].shift(1))
                
                # Calculate Bollinger Bands with minimum period of 5
                bollinger_period = max(5, self.bollinger_period)
                df['bb_upper'], df['bb_middle'], df['bb_lower'] = talib.BBANDS(
                    df['close'], 
                    timeperiod=bollinger_period, 
                    nbdevup=self.bollinger_dev, 
                    nbdevdn=self.bollinger_dev
                )
                
                # Calculate BB width and expansion
                df['bb_width'] = (df['bb_upper'] - df['bb_lower']) / df['bb_middle']
                df['bb_expanding'] = df['bb_width'] > df['bb_width'].shift(1)
                
                # Calculate ATR and range with minimum period of 5
                atr_period = max(5, self.atr_period)
                df['atr'] = talib.ATR(df['high'], df['low'], df['close'], timeperiod=atr_period)
                df['range'] = df['high'].rolling(window=max(5, 10)).max() - df['low'].rolling(window=max(5, 10)).min()
                
            except Exception as e:
                self.logger.error(f"[{symbol}] Error calculating technical indicators: {str(e)}")
                return None
                
            # Handle NaN values
            columns_to_fill = {
                'bool': ['ma_crossover', 'ma_crossunder', 'macd_crossover', 'macd_crossunder', 'bb_expanding'],
                'numeric': ['momentum', 'psar', 'macd', 'macd_signal', 'atr', 'range']
            }
            
            for col in columns_to_fill['bool']:
                if col in df.columns:
                    df[col] = df[col].fillna(False)
                    
            for col in columns_to_fill['numeric']:
                if col in df.columns:
                    df[col] = df[col].fillna(0)
                    
            # Verify all required columns are present and contain valid data
            required_columns = ['ma_crossover', 'momentum', 'close', 'psar', 'macd_crossover', 'bb_expanding']
            missing_columns = [col for col in required_columns if col not in df.columns]
            
            if missing_columns:
                self.logger.error(f"[{symbol}] Missing required columns after calculation: {missing_columns}")
                return None
                
            df.name = (symbol, timeframe)
            return df
            
        except Exception as e:
            self.logger.error(f"[{symbol}] Error in calculate_indicators: {str(e)}")
            return None

    def check_primary_signal(self, df, timeframe, symbol):
        if df is None or len(df) < 20:  # Increased window for better trend analysis
            return None, "Insufficient data", None
    
        try:
            # Verify required columns exist
            required_columns = ['ma_fast', 'ma_slow', 'momentum', 'close', 'psar', 'macd', 'macd_signal', 'bb_upper', 'bb_lower', 'bb_middle', 'open', 'high', 'low']
            missing_columns = [col for col in required_columns if col not in df.columns]
            if missing_columns:
                self.logger.error(f"[{symbol}] Missing required columns: {missing_columns}")
                return None, f"Missing indicators: {', '.join(missing_columns)}", None
    
            # Get the last 20 candles for analysis
            window = df.iloc[-20:].copy()
            latest = window.iloc[-1]    # Latest candle
            prev = window.iloc[-2]      # Previous candle
            signal_time = datetime.now()
    
            # 1. Detect Consolidation (using Bollinger Bands width)
            bb_width = (latest['bb_upper'] - latest['bb_lower']) / latest['bb_middle']
            consolidation = bb_width < 0.05  # Narrow BB indicates consolidation (adjust threshold as needed)
    
            # 2. Check for price interaction with key levels (MA as proxy for support/resistance)
            price_near_ma = abs(latest['close'] - latest['ma_slow']) / latest['ma_slow'] < 0.005  # Price within 0.5% of MA
    
            # 3. MA crossover confirmation (but not the only trigger)
            ma_crossover_buy = latest['ma_fast'] > latest['ma_slow'] and prev['ma_fast'] <= prev['ma_slow']
            ma_crossover_sell = latest['ma_fast'] < latest['ma_slow'] and prev['ma_fast'] >= prev['ma_slow']
    
            # 4. Enhanced momentum analysis
            momentum_window = window['momentum'].tail(5)
            momentum_bullish = (
                latest['momentum'] > 0 and
                momentum_window.mean() > 0 and
                latest['momentum'] > momentum_window.mean()
            )
            momentum_bearish = (
                latest['momentum'] < 0 and
                momentum_window.mean() < 0 and
                latest['momentum'] < momentum_window.mean()
            )
    
            # 5. MACD with zero-line cross and crossover
            macd_bullish = (
                latest['macd'] > latest['macd_signal'] and
                prev['macd'] <= prev['macd_signal'] and  # MACD crossover
                latest['macd'] > 0  # Above zero line
            )
            macd_bearish = (
                latest['macd'] < latest['macd_signal'] and
                prev['macd'] >= prev['macd_signal'] and  # MACD crossover
                latest['macd'] < 0  # Below zero line
            )
    
            # 6. PSAR trend confirmation
            psar_below_price = latest['close'] > latest['psar']
            psar_above_price = latest['close'] < latest['psar']
    
            # 7. Price action confirmation (strong candle after consolidation)
            bullish_candle = latest['close'] > latest['open'] and (latest['close'] - latest['open']) > (latest['high'] - latest['close']) * 0.6
            bearish_candle = latest['close'] < latest['open'] and (latest['open'] - latest['close']) > (latest['close'] - latest['low']) * 0.6
    
            # 8. Buy conditions (wait for breakout after consolidation or key level test)
            buy_conditions_met = (
                (consolidation or price_near_ma) and  # Price in consolidation or near key level
                (ma_crossover_buy or psar_below_price) and  # Trend confirmation
                macd_bullish and  # Momentum confirmation
                momentum_bullish and  # Strong momentum
                bullish_candle  # Strong price action
            )
    
            # 9. Sell conditions (wait for breakdown after consolidation or key level test)
            sell_conditions_met = (
                (consolidation or price_near_ma) and  # Price in consolidation or near key level
                (ma_crossover_sell or psar_above_price) and  # Trend confirmation
                macd_bearish and  # Momentum confirmation
                momentum_bearish and  # Strong momentum
                bearish_candle  # Strong price action
            )
    
            tf_name = self.get_timeframe_name(timeframe)
            if buy_conditions_met:
                message = (
                    f"🚀 PRIMARY STRATEGY SIGNAL 🚀\n"
                    f"Time: {signal_time}\nSymbol: {symbol}\nTimeframe: {tf_name}\nDirection: BUY\n"
                    f"Conditions Met:\n"
                    f"- Setup: {'Consolidation Breakout' if consolidation else 'Support Bounce'}\n"
                    f"- MA/PSAR: {'MA Crossover Up' if ma_crossover_buy else 'PSAR Below Price'}\n"
                    f"- Momentum: {latest['momentum']:.2f} (Bullish)\n"
                    f"- MACD: Bullish Crossover\n"
                    f"- Candle: Strong Bullish"
                )
                return "BUY", message, signal_time
            elif sell_conditions_met:
                message = (
                    f"🚀 PRIMARY STRATEGY SIGNAL 🚀\n"
                    f"Time: {signal_time}\nSymbol: {symbol}\nTimeframe: {tf_name}\nDirection: SELL\n"
                    f"Conditions Met:\n"
                    f"- Setup: {'Consolidation Breakdown' if consolidation else 'Resistance Rejection'}\n"
                    f"- MA/PSAR: {'MA Crossover Down' if ma_crossover_sell else 'PSAR Above Price'}\n"
                    f"- Momentum: {latest['momentum']:.2f} (Bearish)\n"
                    f"- MACD: Bearish Crossover\n"
                    f"- Candle: Strong Bearish"
                )
                return "SELL", message, signal_time
            return None, "No primary signal", None
    
        except Exception as e:
            self.logger.error(f"[{symbol}] Error in check_primary_signal: {str(e)}")
            return None, f"Error checking signal: {str(e)}", None

    def check_suretrend_signal(self, df, timeframe, symbol):
        """Modified SureTrend strategy to capture consolidation breakouts with MA crossover exits."""
        if len(df) < 25:
            return None, "Insufficient data", None
            
        try:
            # Look at recent price action
            window = df.iloc[-15:].copy()
            consolidation_window = df.iloc[-25:-1]  # Look back further for consolidation
            
            latest = df.iloc[-1]
            prev = df.iloc[-2]
            signal_time = datetime.now()

            # 1. Define Consolidation Parameters
            price_range = consolidation_window['high'].max() - consolidation_window['low'].min()
            avg_range = price_range / len(consolidation_window)
            price_std = consolidation_window['close'].std()
            
            # Identify tight consolidation
            consolidation = (
                price_std < consolidation_window['close'].mean() * 0.002 and  # Very tight price action
                avg_range < (latest['bb_upper'] - latest['bb_lower']) * 0.3    # Price range within BB bands
            )

            # 2. Check Moving Average Alignment
            ma_trend_up = latest['ma_fast'] > latest['ma_slow'] and prev['ma_fast'] > prev['ma_slow']
            ma_trend_down = latest['ma_fast'] < latest['ma_slow'] and prev['ma_fast'] < prev['ma_slow']

            # 3. Check MACD for momentum
            macd_increasing = latest['macd'] > prev['macd']
            macd_decreasing = latest['macd'] < prev['macd']
            
            # 4. Check for breakout
            breakout_up = (
                latest['close'] > consolidation_window['high'].max() and
                latest['close'] > latest['bb_middle'] and
                macd_increasing and
                ma_trend_up
            )

            breakout_down = (
                latest['close'] < consolidation_window['low'].min() and
                latest['close'] < latest['bb_middle'] and
                macd_decreasing and
                ma_trend_down
            )

            # Signal Generation
            if consolidation and breakout_up:
                message = (
                    f"🎯 SURETREND BUY SIGNAL\n"
                    f"Time: {signal_time}\n"
                    f"Symbol: {symbol}\n"
                    f"Timeframe: {self.get_timeframe_name(timeframe)}\n"
                    f"Setup: Consolidation Breakout\n"
                    f"Price: {latest['close']:.5f}\n"
                    f"Conditions Met:\n"
                    f"- Tight Consolidation: {price_std:.6f}\n"
                    f"- MACD Direction: Increasing\n"
                    f"- MA Trend: Bullish\n"
                    f"- Exit Condition: Bearish MA Crossover"
                )
                return "BUY", message, signal_time

            elif consolidation and breakout_down:
                message = (
                    f"🎯 SURETREND SELL SIGNAL\n"
                    f"Time: {signal_time}\n"
                    f"Symbol: {symbol}\n"
                    f"Timeframe: {self.get_timeframe_name(timeframe)}\n"
                    f"Setup: Consolidation Breakdown\n"
                    f"Price: {latest['close']:.5f}\n"
                    f"Conditions Met:\n"
                    f"- Tight Consolidation: {price_std:.6f}\n"
                    f"- MACD Direction: Decreasing\n"
                    f"- MA Trend: Bearish\n"
                    f"- Exit Condition: Bullish MA Crossover"
                )
                return "SELL", message, signal_time

            return None, "No SureTrend signal", None

        except Exception as e:
            self.logger.error(f"Error in SureTrend strategy for {symbol}: {str(e)}")
            return None, f"Error: {str(e)}", None


    def check_momentum_strategy(self, df, timeframe, symbol):
        """
        Modified momentum strategy using MACD histogram for momentum detection
        with MA crossover exits and trailing stop management
        """
        if df is None or len(df) < 20:
            return None, "Insufficient data", None

        try:
            # Get recent price action
            window = df.iloc[-20:].copy()
            latest = window.iloc[-1]
            prev = window.iloc[-2]
            signal_time = datetime.now()

            # 1. Detect prior consolidation (past 15-20 bars)
            consolidation_window = df.iloc[-20:-1]
            price_range = consolidation_window['high'].max() - consolidation_window['low'].min()
            avg_range = price_range / len(consolidation_window)
            price_std = consolidation_window['close'].std()
            
            consolidation_present = (
                price_std < consolidation_window['close'].mean() * 0.002 and
                avg_range < (latest['bb_upper'] - latest['bb_lower']) * 0.3
            )

            # 2. Check for MACD histogram momentum
            macd_hist = latest['macd'] - latest['macd_signal']
            prev_hist = prev['macd'] - prev['macd_signal']
            hist_increasing = macd_hist > prev_hist
            
            strong_momentum = (
                abs(macd_hist) > abs(window['macd'].mean()) and
                hist_increasing and
                macd_hist > 0  # For bullish momentum
            )

            weak_momentum = (
                abs(macd_hist) > abs(window['macd'].mean()) and
                not hist_increasing and
                macd_hist < 0  # For bearish momentum
            )

            # 3. Check MA alignment
            ma_aligned_bullish = (
                latest['ma_fast'] > latest['ma_slow'] > latest['ema_20'] and
                latest['close'] > latest['ma_fast']
            )

            ma_aligned_bearish = (
                latest['ma_fast'] < latest['ma_slow'] < latest['ema_20'] and
                latest['close'] < latest['ma_fast']
            )

            # 4. Check MACD crossover conditions
            macd_bullish = (
                latest['macd'] > latest['macd_signal'] and
                prev['macd'] <= prev['macd_signal'] and
                latest['macd'] > 0
            )

            macd_bearish = (
                latest['macd'] < latest['macd_signal'] and
                prev['macd'] >= prev['macd_signal'] and
                latest['macd'] < 0
            )

            # 5. Confirm with price action
            strong_bullish_candle = (
                latest['close'] > latest['open'] and
                (latest['close'] - latest['open']) > (latest['high'] - latest['close']) * 0.7
            )

            strong_bearish_candle = (
                latest['close'] < latest['open'] and
                (latest['open'] - latest['close']) > (latest['close'] - latest['low']) * 0.7
            )

            # Buy conditions
            buy_conditions = (
                consolidation_present and
                strong_momentum and
                ma_aligned_bullish and
                macd_bullish and
                strong_bullish_candle
            )

            # Sell conditions
            sell_conditions = (
                consolidation_present and
                weak_momentum and
                ma_aligned_bearish and
                macd_bearish and
                strong_bearish_candle
            )

            # Calculate dynamic stop levels using ATR
            atr = latest['atr']
            stop_distance = 2 * atr
            trailing_stop = 1.5 * atr
            breakeven_level = 1.0 * atr
            trailing_activation = 1.2 * atr

            if buy_conditions:
                entry_price = latest['close']
                sl_price = entry_price - stop_distance
                tp_price = entry_price + (stop_distance * 2)

                message = (
                    f"💨 MOMENTUM STRATEGY SIGNAL 💨\n"
                    f"Time: {signal_time}\n"
                    f"Symbol: {symbol}\n"
                    f"Timeframe: {self.get_timeframe_name(timeframe)}\n"
                    f"Price: {entry_price:.5f}\n"
                    f"Setup: MACD Histogram Momentum Break\n"
                    f"Conditions Met:\n"
                    f"- Prior Consolidation: {price_std:.6f}\n"
                    f"- MACD Histogram: {macd_hist:.6f}\n"
                    f"- Histogram Momentum: Increasing\n"
                    f"- MA Alignment: Bullish\n"
                    f"Stop Management:\n"
                    f"- Initial Stop: -{stop_distance:.5f} points\n"
                    f"- Trailing Stop: {trailing_stop:.5f} points\n"
                    f"- Breakeven at: +{breakeven_level:.5f} points\n"
                    f"- Trail Activation: +{trailing_activation:.5f} points\n"
                    f"Exit: Bearish MA Crossover"
                )

                return Signal(
                    strategy_name="MOMENTUM",
                    signal_type=SignalType.LONG,
                    entry_price=entry_price,
                    stop_loss=sl_price,
                    take_profit=tp_price,
                    trailing_stop=trailing_stop,
                    trailing_stop_delay=trailing_activation,
                    break_even=breakeven_level,
                    message=message
                )

            elif sell_conditions:
                entry_price = latest['close']
                sl_price = entry_price + stop_distance
                tp_price = entry_price - (stop_distance * 2)

                message = (
                    f"💨 MOMENTUM STRATEGY SIGNAL 💨\n"
                    f"Time: {signal_time}\n"
                    f"Symbol: {symbol}\n"
                    f"Timeframe: {self.get_timeframe_name(timeframe)}\n"
                    f"Price: {entry_price:.5f}\n"
                    f"Setup: MACD Histogram Momentum Break\n"
                    f"Conditions Met:\n"
                    f"- Prior Consolidation: {price_std:.6f}\n"
                    f"- MACD Histogram: {macd_hist:.6f}\n"
                    f"- Histogram Momentum: Decreasing\n"
                    f"- MA Alignment: Bearish\n"
                    f"Stop Management:\n"
                    f"- Initial Stop: +{stop_distance:.5f} points\n"
                    f"- Trailing Stop: {trailing_stop:.5f} points\n"
                    f"- Breakeven at: -{breakeven_level:.5f} points\n"
                    f"- Trail Activation: -{trailing_activation:.5f} points\n"
                    f"Exit: Bullish MA Crossover"
                )

                return Signal(
                    strategy_name="MOMENTUM",
                    signal_type=SignalType.SHORT,
                    entry_price=entry_price,
                    stop_loss=sl_price,
                    take_profit=tp_price,
                    trailing_stop=trailing_stop,
                    trailing_stop_delay=trailing_activation,
                    break_even=breakeven_level,
                    message=message
                )

            return None, "No momentum signal", None

        except Exception as e:
            self.logger.error(f"[{symbol}] Error in momentum strategy: {str(e)}")
            return None, f"Error in momentum strategy: {str(e)}", None

    def check_grid_signal(self, df, timeframe, symbol):
        if not self.grid_trading_enabled:
            return None, "Grid trading disabled", None
        
        try:
            # Get the last 10 candles for analysis
            window = df.iloc[-10:].copy()
            latest = window.iloc[-1]    # Latest candle
            prev = window.iloc[-2]      # Previous candle
            signal_time = datetime.now()
            
            # Get current positions for this symbol
            grid_positions = [p for p in self.positions[symbol].values() if p.get('strategy') == 'grid']
            if len(grid_positions) >= self.grid_levels:
                return None, "Grid level limit reached", None
            
            # Calculate current price and grid levels
            current_price = latest['close']
            base_price = round(current_price / (self.grid_spacing * self.point[symbol])) * (self.grid_spacing * self.point[symbol])
            
            # Calculate grid levels
            buy_levels = [base_price - i * self.grid_spacing * self.point[symbol] for i in range(1, self.grid_levels + 1)]
            sell_levels = [base_price + i * self.grid_spacing * self.point[symbol] for i in range(1, self.grid_levels + 1)]
            
            # Check price trend in recent candles
            price_falling = all(window['close'].iloc[i] < window['close'].iloc[i-1] for i in range(-1, -4, -1))
            price_rising = all(window['close'].iloc[i] > window['close'].iloc[i-1] for i in range(-1, -4, -1))
            
            # Check volatility
            volatility = window['high'].max() - window['low'].min()
            avg_volatility = volatility / len(window)
            volatility_suitable = avg_volatility <= self.grid_spacing * self.point[symbol] * 2  # Volatility should be manageable
            
            tf_name = self.get_timeframe_name(timeframe)
            
            # Check buy conditions with trend confirmation
            for level in buy_levels:
                if (current_price <= level and 
                    price_falling and 
                    volatility_suitable and 
                    not any(abs(p['entry_price'] - level) < self.point[symbol] for p in grid_positions)):
                    
                    message = (
                        f"📊 GRID STRATEGY SIGNAL 📊\n"
                        f"Time: {signal_time}\nSymbol: {symbol}\nTimeframe: {tf_name}\nDirection: BUY\n"
                        f"Conditions Met:\n"
                        f"- Price at Grid Level: {level:.5f}\n"
                        f"- Price Trend: Falling (3 candles)\n"
                        f"- Volatility: {'Suitable' if volatility_suitable else 'High'}\n"
                        f"- Grid Spacing: {self.grid_spacing} points\n"
                        f"- Active Grid Positions: {len(grid_positions)}/{self.grid_levels}"
                    )
                    return "BUY", message, signal_time
            
            # Check sell conditions with trend confirmation
            for level in sell_levels:
                if (current_price >= level and 
                    price_rising and 
                    volatility_suitable and 
                    not any(abs(p['entry_price'] - level) < self.point[symbol] for p in grid_positions)):
                    
                    message = (
                        f"📊 GRID STRATEGY SIGNAL 📊\n"
                        f"Time: {signal_time}\nSymbol: {symbol}\nTimeframe: {tf_name}\nDirection: SELL\n"
                        f"Conditions Met:\n"
                        f"- Price at Grid Level: {level:.5f}\n"
                        f"- Price Trend: Rising (3 candles)\n"
                        f"- Volatility: {'Suitable' if volatility_suitable else 'High'}\n"
                        f"- Grid Spacing: {self.grid_spacing} points\n"
                        f"- Active Grid Positions: {len(grid_positions)}/{self.grid_levels}"
                    )
                    return "SELL", message, signal_time
            
            return None, "No grid signal", None
            
        except Exception as e:
            self.logger.error(f"[{symbol}] Error in check_grid_signal: {str(e)}")
            return None, f"Error checking signal: {str(e)}", None

    def check_breakout_momentum_signal(self, df, timeframe, symbol):
        """
        Check for consolidation breakout with momentum confirmation.
        Returns: (direction, message, signal_time) or (None, reason, None)
        """
        if not self.breakout_momentum_enabled:
            return None, "Breakout Momentum strategy disabled", None
    
        try:
            if df is None or len(df) < self.consolidation_lookback + 1:
                return None, f"Insufficient data (need at least {self.consolidation_lookback + 1} bars)", None
    
            # Get recent price action
            consolidation_window = df.iloc[-self.consolidation_lookback-1:-1]  # Exclude latest candle
            latest = df.iloc[-1]
            prev = df.iloc[-2]
            signal_time = datetime.now()
    
            # 1. Detect Consolidation
            # Bollinger Band width should be below threshold
            bb_width = (consolidation_window['bb_upper'] - consolidation_window['bb_lower']) / consolidation_window['bb_middle']
            avg_bb_width = bb_width.mean()
            consolidation = avg_bb_width < self.consolidation_threshold
    
            # Price range should be tight
            price_range = consolidation_window['high'].max() - consolidation_window['low'].min()
            avg_price_range = price_range / len(consolidation_window)
            price_std = consolidation_window['close'].std()
            tight_range = price_std < consolidation_window['close'].mean() * 0.002  # Adjust threshold as needed
    
            if not (consolidation and tight_range):
                return None, "No consolidation detected", None
    
            # 2. Detect Breakout
            consolidation_high = consolidation_window['high'].max()
            consolidation_low = consolidation_window['low'].min()
            breakout_up = latest['close'] > consolidation_high and latest['close'] > latest['bb_middle']
            breakout_down = latest['close'] < consolidation_low and latest['close'] < latest['bb_middle']
    
            # Confirm with strong candle
            bullish_candle = latest['close'] > latest['open'] and (latest['close'] - latest['open']) > (latest['high'] - latest['close']) * 0.6
            bearish_candle = latest['close'] < latest['open'] and (latest['open'] - latest['close']) > (latest['close'] - latest['low']) * 0.6
    
            # 3. Confirm with MA Alignment
            ma_trend_up = latest['ma_fast'] > latest['ma_slow'] and prev['ma_fast'] <= prev['ma_slow']  # Bullish crossover
            ma_trend_down = latest['ma_fast'] < latest['ma_slow'] and prev['ma_fast'] >= prev['ma_slow']  # Bearish crossover
    
            # 4. Confirm with MACD Momentum
            macd_bullish = (
                latest['macd'] > latest['macd_signal'] and
                prev['macd'] <= prev['macd_signal'] and  # MACD crossover
                latest['macd'] > 0  # Above zero line
            )
            macd_bearish = (
                latest['macd'] < latest['macd_signal'] and
                prev['macd'] >= prev['macd_signal'] and  # MACD crossover
                latest['macd'] < 0  # Below zero line
            )
    
            # 5. Confirm with RSI (avoid overbought/oversold conditions)
            rsi_valid_buy = latest['rsi'] < self.rsi_overbought
            rsi_valid_sell = latest['rsi'] > self.rsi_oversold
    
            # 6. Confirm with PSAR
            psar_bullish = latest['close'] > latest['psar']
            psar_bearish = latest['close'] < latest['psar']
    
            # 7. Buy Conditions
            buy_conditions = (
                breakout_up and
                bullish_candle and
                ma_trend_up and
                macd_bullish and
                rsi_valid_buy and
                psar_bullish
            )
    
            # 8. Sell Conditions
            sell_conditions = (
                breakout_down and
                bearish_candle and
                ma_trend_down and
                macd_bearish and
                rsi_valid_sell and
                psar_bearish
            )
    
            # 9. Generate Signal
            tf_name = self.get_timeframe_name(timeframe)
            if buy_conditions:
                entry_price = latest['close']
                # Calculate TP/SL
                consolidation_height = consolidation_high - consolidation_low
                atr = latest['atr']
                tp = entry_price + (consolidation_height * self.breakout_multiplier)
                sl = entry_price - (atr * self.atr_multiplier_sl)
                trailing_stop = atr * self.atr_multiplier_trailing
    
                message = (
                    f"💥 BREAKOUT MOMENTUM BUY SIGNAL 💥\n"
                    f"Time: {signal_time}\n"
                    f"Symbol: {symbol}\n"
                    f"Timeframe: {tf_name}\n"
                    f"Price: {entry_price:.5f}\n"
                    f"Setup: Consolidation Breakout\n"
                    f"Conditions Met:\n"
                    f"- BB Width: {avg_bb_width:.4f} (Consolidated)\n"
                    f"- Price Range: {price_range:.5f}\n"
                    f"- MA Crossover: Bullish\n"
                    f"- MACD: Bullish Crossover\n"
                    f"- RSI: {latest['rsi']:.2f} (Not Overbought)\n"
                    f"- PSAR: Below Price\n"
                    f"Targets:\n"
                    f"- TP: {tp:.5f} (+{consolidation_height * self.breakout_multiplier:.5f})\n"
                    f"- SL: {sl:.5f} (-{atr * self.atr_multiplier_sl:.5f})\n"
                    f"- Trailing Stop: {trailing_stop:.5f}\n"
                    f"Exit: Bearish MA Crossover"
                )
                return "BUY", message, signal_time
    
            elif sell_conditions:
                entry_price = latest['close']
                # Calculate TP/SL
                consolidation_height = consolidation_high - consolidation_low
                atr = latest['atr']
                tp = entry_price - (consolidation_height * self.breakout_multiplier)
                sl = entry_price + (atr * self.atr_multiplier_sl)
                trailing_stop = atr * self.atr_multiplier_trailing
    
                message = (
                    f"💥 BREAKOUT MOMENTUM SELL SIGNAL 💥\n"
                    f"Time: {signal_time}\n"
                    f"Symbol: {symbol}\n"
                    f"Timeframe: {tf_name}\n"
                    f"Price: {entry_price:.5f}\n"
                    f"Setup: Consolidation Breakdown\n"
                    f"Conditions Met:\n"
                    f"- BB Width: {avg_bb_width:.4f} (Consolidated)\n"
                    f"- Price Range: {price_range:.5f}\n"
                    f"- MA Crossover: Bearish\n"
                    f"- MACD: Bearish Crossover\n"
                    f"- RSI: {latest['rsi']:.2f} (Not Oversold)\n"
                    f"- PSAR: Above Price\n"
                    f"Targets:\n"
                    f"- TP: {tp:.5f} (-{consolidation_height * self.breakout_multiplier:.5f})\n"
                    f"- SL: {sl:.5f} (+{atr * self.atr_multiplier_sl:.5f})\n"
                    f"- Trailing Stop: {trailing_stop:.5f}\n"
                    f"Exit: Bullish MA Crossover"
                )
                return "SELL", message, signal_time
    
            return None, "No Breakout Momentum signal", None
    
        except Exception as e:
            self.logger.error(f"[{symbol}] Error in BreakoutMomentum strategy: {str(e)}")
            return None, f"Error in BreakoutMomentum strategy: {str(e)}", None

    def check_exit_signal(self, position, df):
        """Modified exit signal check with specific handling for strategies"""
        timeframe = position['timeframe']
        strategy = position.get('strategy', 'primary')
    
        # For SureTrend and BreakoutMomentum, use MA crossover exits
        if strategy in ['suretrend', 'breakout_momentum']:
            latest = df.iloc[-1]
            prev = df.iloc[-2]
    
            # Check for opposite MA crossover
            if position['type'] == mt5.ORDER_TYPE_BUY:
                # Exit long on bearish crossover
                if latest['ma_fast'] < latest['ma_slow'] and prev['ma_fast'] >= prev['ma_slow']:
                    return True, f"{strategy.upper()} MA crossover exit signal (bearish)"
            else:
                # Exit short on bullish crossover
                if latest['ma_fast'] > latest['ma_slow'] and prev['ma_fast'] <= prev['ma_slow']:
                    return True, f"{strategy.upper()} MA crossover exit signal (bullish)"
            return False, f"No {strategy} exit signal"
    
        # Default exit check for other strategies
        latest = df.iloc[-1]
        prev = df.iloc[-2]
        crossunder = prev['exit_ma_fast'] >= prev['exit_ma_slow'] and latest['exit_ma_fast'] < latest['exit_ma_slow']
        crossover = prev['exit_ma_fast'] <= prev['exit_ma_slow'] and latest['exit_ma_fast'] > latest['exit_ma_slow']
    
        if position['type'] == mt5.ORDER_TYPE_BUY and crossunder:
            return True, f"Exit MA {self.ma_configs[position['timeframe']]['exit_fast']}/{self.ma_configs[position['timeframe']]['exit_slow']} crossover down"
        elif position['type'] == mt5.ORDER_TYPE_SELL and crossover:
            return True, f"Exit MA {self.ma_configs[position['timeframe']]['exit_fast']}/{self.ma_configs[position['timeframe']]['exit_slow']} crossover up"
        return False, "No exit signal"

    def check_volatility(self, df):
        latest = df.iloc[-1]
        avg_atr = df['atr'].mean()
        avg_range = df['range'].mean()
        return "high_volatility" if (latest['atr'] > 3 * avg_atr or latest['range'] > 3 * avg_range) else "normal"

    def check_manual_trade_conditions(self, symbol, timeframe, direction):
        df = self.get_or_update_rates(symbol, timeframe)
        if df is None or len(df) < 10:
            return False, "Failed to fetch rates or insufficient data"
        window = df.iloc[-10:]
        latest = df.iloc[-1]
        prev = df.iloc[-2]
        
        ma_crossover = window['ma_crossover'].any() if direction == "BUY" else window['ma_crossunder'].any()
        momentum_valid = (
            (direction == "BUY" and (window['momentum'] > 0).any() and latest['momentum'] > prev['momentum']) or
            (direction == "SELL" and (window['momentum'] < 0).any() and latest['momentum'] < prev['momentum'])
        )
        confirmations = sum([
            (window['close'] > window['psar']).any() if direction == "BUY" else (window['close'] < window['psar']).any(),
            window['macd_crossover'].any() if direction == "BUY" else window['macd_crossunder'].any(),
            window['bb_expanding'].any()
        ])
        
        if not ma_crossover:
            return False, "No MA crossover detected"
        if not momentum_valid:
            return False, "Momentum conditions not met"
        if confirmations < 1:
            return False, "Insufficient confirmation signals"
        return True, f"MA crossover confirmed, Momentum: {latest['momentum']:.2f}, Confirmations: {confirmations}"

    def calculate_suretrend_tp_sl(self, df, signal_type, entry_price):
        """Calculate SureTrend strategy specific TP/SL levels"""
        consolidation_height = df['high'].iloc[-50:-1].max() - df['low'].iloc[-50:-1].min()
        atr = df['atr'].iloc[-1]
        
        if signal_type == "BUY":
            sl = entry_price - max(consolidation_height * 0.3, atr * 1.5)
            tp = entry_price + (consolidation_height * 1.5)
        else:
            sl = entry_price + max(consolidation_height * 0.3, atr * 1.5)
            tp = entry_price - (consolidation_height * 1.5)
            
        return tp, sl

    def calculate_lot_size(self, symbol, entry_price, sl_price):
        """Calculate lot size based on risk management rules using MT5 data"""
        if self.simulate:
            return self.lot_size

        try:
            # Get account info
            account_info = mt5.account_info()
            if not account_info:
                return self.lot_size

            # Get symbol info
            symbol_info = mt5.symbol_info(symbol)
            if not symbol_info:
                return self.lot_size

            # Calculate risk amount
            risk_amount = account_info.balance * (self.risk_percent / 100)
            
            # Calculate pip value
            contract_size = symbol_info.trade_contract_size
            point_value = symbol_info.trade_tick_value
            
            # Calculate distance in points
            point_distance = abs(entry_price - sl_price) / symbol_info.point
            
            # Calculate required lot size
            lot_size = (risk_amount / (point_distance * point_value))
            
            # Round to valid lot size
            lot_size = round(lot_size / symbol_info.volume_step) * symbol_info.volume_step
            
            # Ensure within limits
            lot_size = max(symbol_info.volume_min, min(symbol_info.volume_max, lot_size))
            
            return lot_size

        except Exception as e:
            self.logger.error(f"Error calculating lot size: {e}")
            return self.lot_size

    def open_position(self, order_type, entry_price, signal_time, signal_message, timeframe, symbol, strategy="primary"):
        """
        Open a new trading position with parameter prompting.
        """
        self.logger.debug(f"[{symbol}] Entering open_position: order_type={order_type}, entry_price={entry_price}, timeframe={timeframe}, strategy={strategy}")
        self.logger.debug(f"[{symbol}] self.point contents: {self.point}")
    
        if not self.ensure_mt5_connection() and not self.simulate:
            self.logger.error(f"[{symbol}] Cannot open position: MT5 connection not established")
            return False, None
        
        try:
            # Get latest data to verify indicators
            df = self.get_or_update_rates(symbol, timeframe)
            if df is None:
                self.logger.error(f"[{symbol}] Cannot open position: Failed to get latest data")
                return False, None
                
            # Calculate indicators
            df = self.calculate_indicators(df, timeframe, symbol)
            if df is None:
                self.logger.error(f"[{symbol}] Cannot open position: Failed to calculate indicators")
                return False, None
    
            # Get point value from point dictionary with fallback
            point = self.point.get(symbol, 0.01)
            self.logger.debug(f"[{symbol}] Point value: {point} (type: {type(point)}), symbol in self.point: {symbol in self.point}")
            if symbol not in self.point or self.point[symbol] is None:
                self.logger.warning(f"[{symbol}] Point value not found, using fallback: {point}")
    
            # Verify trading is allowed
            if not self.simulate:
                terminal_info = mt5.terminal_info()
                if not terminal_info or not terminal_info.trade_allowed:
                    self.logger.error(f"[{symbol}] Cannot open position: AutoTrading is disabled in MT5 terminal")
                    return False, None
            
                # Get symbol info
                symbol_info = mt5.symbol_info(symbol)
                if not symbol_info:
                    self.logger.error(f"[{symbol}] Failed to get symbol info")
                    return False, None
            
                if not symbol_info.trade_mode:
                    self.logger.error(f"[{symbol}] Trading is not allowed for {symbol}")
                    return False, None
    
            # Calculate default SL/TP based on ATR
            atr = df['atr'].iloc[-1] if 'atr' in df.columns else self.initial_sl * point
            default_sl = entry_price - (2 * atr) if order_type == mt5.ORDER_TYPE_BUY else entry_price + (2 * atr)
            default_tp = entry_price + (3 * atr) if order_type == mt5.ORDER_TYPE_BUY else entry_price - (3 * atr)
    
            # Calculate lot size based on risk
            lot_size = self.calculate_lot_size(symbol, entry_price, default_sl)
        
            if self.simulate:
                ticket = random.randint(100000, 999999)
                position = {
                    "ticket": ticket,
                    "type": order_type,
                    "entry_price": entry_price,
                    "sl": default_sl,
                    "tp": default_tp,
                    "entry_time": datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f'),
                    "signal_time": signal_time,
                    "breakeven_triggered": False,
                    "trailing_active": False,
                    "timeframe": timeframe,
                    "reason": strategy.capitalize(),
                    "comments": "GC_Signals Trade",
                    "lot_size": lot_size,
                    "symbol": symbol,
                    "strategy": strategy,
                    "profit": 0.0,
                    "status": "open",
                    "script_placed": True,
                    "waiting_params": True
                }
                
                with self.command_lock:
                    self.positions[symbol][ticket] = position
                    self.add_to_trade_history(position)
                
                self.prompt_position_params(position)
                self.logger.info(f"[{symbol}] Simulated position opened: Ticket={ticket}")
                return True, position
                
            else:
                request = {
                    "action": mt5.TRADE_ACTION_DEAL,
                    "symbol": symbol,
                    "volume": lot_size,
                    "type": order_type,
                    "price": entry_price,
                    "sl": default_sl,
                    "tp": default_tp,
                    "deviation": self.deviation,
                    "magic": 234000,
                    "comment": f"GC_Signals_{strategy.capitalize()}",
                    "type_time": mt5.ORDER_TIME_GTC,
                    "type_filling": mt5.ORDER_FILLING_IOC
                }
    
                for attempt in range(self.max_retries):
                    result = mt5.order_send(request)
                    if result is None:
                        self.logger.error(f"[{symbol}] Order send failed: {mt5.last_error()}")
                        time.sleep(self.retry_delay)
                        continue
    
                    if result.retcode == mt5.TRADE_RETCODE_DONE:
                        position = {
                            "ticket": result.order,
                            "type": order_type,
                            "entry_price": entry_price,
                            "sl": default_sl,
                            "tp": default_tp,
                            "entry_time": datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f'),
                            "signal_time": signal_time,
                            "breakeven_triggered": False,
                            "trailing_active": False,
                            "timeframe": timeframe,
                            "reason": strategy.capitalize(),
                            "comments": f"GC_Signals_{strategy.capitalize()}",
                            "lot_size": lot_size,
                            "symbol": symbol,
                            "strategy": strategy,
                            "profit": 0.0,
                            "status": "open",
                            "script_placed": True,
                            "waiting_params": True
                        }
    
                        df = self.get_rates(symbol, timeframe=timeframe)
                        df = self.calculate_indicators(df, timeframe, symbol)
                        chart_path = self.generate_chart(df, "Entry", timeframe, symbol, entry_price=entry_price)
                        
                        initial_message = (
                            f"{signal_message}\n"
                            f"Entry: {entry_price:.5f}\n"
                            f"Initial SL: {default_sl:.5f}\n"
                            f"Initial TP: {default_tp:.5f}\n"
                            f"Lot Size: {lot_size}\n"
                            f"Ticket: {result.order}"
                        )
                        
                        position["thread_id"] = self.send_telegram_message(initial_message, chart_path=chart_path)
    
                        with self.command_lock:
                            self.positions[symbol][result.order] = position
                            self.add_to_trade_history(position)
    
                        self.prompt_position_params(position)
                        self.logger.info(f"[{symbol}] Position opened: Ticket={result.order}")
                        return True, position
    
                    if result.retcode == mt5.TRADE_RETCODE_REQUOTE:
                        self.logger.warning(f"[{symbol}] Requote detected, retrying...")
                        continue
                    if result.retcode == mt5.TRADE_RETCODE_INVALID_PRICE:
                        self.logger.error(f"[{symbol}] Invalid price: {entry_price}")
                        return False, None
    
                    self.logger.error(f"[{symbol}] Order failed: {result.comment} (retcode: {result.retcode})")
                    return False, None
    
                self.logger.error(f"[{symbol}] Failed to open position after {self.max_retries} attempts")
                return False, None
    
        except Exception as e:
            self.logger.error(f"[{symbol}] Error in open_position: {str(e)}", exc_info=True)
            return False, None

    def add_to_trade_history(self, position):
        """Add trade to appropriate history list"""
        history_entry = {
            "ticket": position["ticket"],
            "type": "BUY" if position["type"] == mt5.ORDER_TYPE_BUY else "SELL",
            "profit": 0.0,
            "profit_points": 0.0,
            "timeframe": self.get_timeframe_name(position["timeframe"]),
            "entry_time": position["entry_time"],
            "symbol": position["symbol"],
            "status": position["status"],
            "lot_size": position["lot_size"],
            "entry_price": position["entry_price"],
            "sl": position["sl"],
            "tp": position["tp"],
            "strategy": position["strategy"]
        }

        self.daily_trades[position["symbol"]].append(history_entry)
        
        if position["strategy"] == "grid":
            self.grid_history[position["symbol"]].append(history_entry)
        elif position["strategy"] == "suretrend":
            self.suretrend_history[position["symbol"]].append(history_entry)
        elif position["strategy"] == "momentum":
            self.momentum_history[position["symbol"]].append(history_entry)
        else:
            self.trade_history[position["symbol"]].append(history_entry)

        self.save_trade_history()

    def manage_suretrend_position(self, position, current_price, df):
        """Enhanced position management for SureTrend trades"""
        profit_points = self.convert_to_points(
            current_price - position['entry_price'] if position['type'] == mt5.ORDER_TYPE_BUY 
            else position['entry_price'] - current_price, 
            position['symbol']
        )
        
        # Move to breakeven after 1x consolidation height
        if profit_points > position['consolidation_height'] and not position['breakeven_triggered']:
            self.modify_position(position, sl=position['entry_price'])
            position['breakeven_triggered'] = True
        
        # Trail stop after 1.5x consolidation height
        if profit_points > position['consolidation_height'] * 1.5 and not position['trailing_active']:
            trail_distance = position['consolidation_height'] * 0.3
            if position['type'] == mt5.ORDER_TYPE_BUY:
                new_sl = current_price - trail_distance
            else:
                new_sl = current_price + trail_distance
            self.modify_position(position, sl=new_sl)
            position['trailing_active'] = True

    def manage_position(self, position, current_price, df):
        """Enhanced position management with strategy-specific handlers."""
        if not self.dynamic_management_enabled:
            return
            
        try:
            # Call strategy-specific handlers
            if position['strategy'] == 'hfscalper':
                self.handle_hfscalper_trade(position['symbol'], df)
            elif position['strategy'] == 'breakout_momentum':
                self.handle_breakout_momentum_trade(position['symbol'], df)
            elif position['strategy'] == 'suretrend':
                self.handle_suretrend_position(position, current_price, df)
            else:
                # Default position management
                symbol = position['symbol']
                profit_points = (current_price - position['entry_price']) / self.point[symbol] if position['type'] == mt5.ORDER_TYPE_BUY else \
                            (position['entry_price'] - current_price) / self.point[symbol]
                
                if profit_points >= self.breakeven_configs[position['timeframe']] and not position['breakeven_triggered']:
                    self.modify_position(position, sl=position['entry_price'])
                    position['breakeven_triggered'] = True
                
                if profit_points >= self.trailing_delay_configs[position['timeframe']] and not position['trailing_active']:
                    trail_points = self.trailing_stop_configs[position['timeframe']]
                    if position['type'] == mt5.ORDER_TYPE_BUY:
                        new_sl = current_price - (trail_points * self.point[symbol])
                        if new_sl > position['sl']:
                            self.modify_position(position, sl=new_sl)
                            position['trailing_active'] = True
                    else:
                        new_sl = current_price + (trail_points * self.point[symbol])
                        if new_sl < position['sl']:
                            self.modify_position(position, sl=new_sl)
                            position['trailing_active'] = True
                            
        except Exception as e:
            self.logger.error(f"Error in manage_position: {str(e)}")

    def modify_position(self, position, sl=None, tp=None):
        symbol = position['symbol']
        if self.simulate:
            if sl is not None:
                position['sl'] = sl
                self.logger.info(f"[{symbol}] Simulated SL modified to {sl:.5f} for ticket {position['ticket']}")
            if tp is not None:
                position['tp'] = tp
                self.logger.info(f"[{symbol}] Simulated TP modified to {tp:.5f} for ticket {position['ticket']}")
            return
        
        request = {
            "action": mt5.TRADE_ACTION_SLTP, "position": position['ticket'],
            "sl": sl if sl is not None else position['sl'],
            "tp": tp if tp is not None else position['tp']
        }
        result = mt5.order_send(request)
        if result.retcode == mt5.TRADE_RETCODE_DONE:
            if sl is not None:
                position['sl'] = sl
                self.logger.info(f"[{symbol}] SL modified to {sl:.5f} for ticket {position['ticket']}")
            if tp is not None:
                position['tp'] = tp
                self.logger.info(f"[{symbol}] TP modified to {tp:.5f} for ticket {position['ticket']}")
        else:
            self.logger.error(f"[{symbol}] Failed to modify position {position['ticket']}: {result.comment}")

    def close_position(self, position, reason):
        symbol = position['symbol']
        ticket = position['ticket']
        timeframe = position['timeframe']
        
        try:
            # First verify if position still exists in MT5
            if not self.simulate:
                mt5_position = mt5.positions_get(ticket=ticket)
                if mt5_position is None or len(mt5_position) == 0:
                    self.logger.info(f"[{symbol}] Position {ticket} already closed in MT5, updating local state")
                    # Use a timeout context for the lock to prevent deadlocks
                    if self.command_lock.acquire(timeout=5):
                        try:
                            if ticket in self.positions[symbol]:
                                del self.positions[symbol][ticket]
                        finally:
                            self.command_lock.release()
                    else:
                        self.logger.error(f"[{symbol}] Failed to acquire lock for updating closed position {ticket}")
                    return True

            if self.simulate:
                df = self.data_cache[symbol][timeframe]['df']
                current_price = df['close'].iloc[-1] if df is not None and not df.empty else position['entry_price']
                profit_points = (current_price - position['entry_price']) / self.point[symbol] if position['type'] == mt5.ORDER_TYPE_BUY else \
                              (position['entry_price'] - current_price) / self.point[symbol]
                position['profit'] = profit_points * self.point[symbol] * position['lot_size'] * 10000
                
                # Use a timeout context for the lock to prevent deadlocks
                if not self.command_lock.acquire(timeout=5):
                    self.logger.error(f"[{symbol}] Failed to acquire lock for closing ticket {ticket}")
                    return False
                
                try:
                    self.daily_profit[symbol] += position['profit']
                    self.update_trade_history_on_close(ticket, symbol, profit_points, reason)
                    del self.positions[symbol][ticket]
                finally:
                    self.command_lock.release()
                
                chart_path = self.generate_chart(df, "Exit", timeframe, symbol, position=position)
                self.send_telegram_message(
                    f"[{symbol}] Closed ticket {ticket}: Profit={profit_points:.2f} points, Reason={reason}",
                    position['thread_id'],
                    chart_path
                )
                return True
            
            else:
                # Get current market price
                tick = mt5.symbol_info_tick(symbol)
                if tick is None:
                    self.logger.error(f"[{symbol}] Failed to get tick data for closing ticket {ticket}")
                    return False
                
                request = {
                    "action": mt5.TRADE_ACTION_DEAL,
                    "symbol": symbol,
                    "volume": position['lot_size'],
                    "type": mt5.ORDER_TYPE_SELL if position['type'] == mt5.ORDER_TYPE_BUY else mt5.ORDER_TYPE_BUY,
                    "position": ticket,
                    "price": tick.bid if position['type'] == mt5.ORDER_TYPE_BUY else tick.ask,
                    "deviation": self.deviation,
                    "magic": 234000,
                    "comment": f"Close: {reason}",
                    "type_time": mt5.ORDER_TIME_GTC,
                    "type_filling": mt5.ORDER_FILLING_IOC
                }
                
                # Try to close the position with retries
                for attempt in range(3):
                    result = mt5.order_send(request)
                    if result is None:
                        error = mt5.last_error()
                        if error[0] == 10013:  # Position already closed
                            self.logger.info(f"[{symbol}] Position {ticket} appears to be already closed")
                            # Use a timeout context for the lock
                            if self.command_lock.acquire(timeout=5):
                                try:
                                    if ticket in self.positions[symbol]:
                                        del self.positions[symbol][ticket]
                                finally:
                                    self.command_lock.release()
                            return True
                        self.logger.error(f"[{symbol}] Failed to close ticket {ticket}: {error}")
                        time.sleep(1)
                        continue
                    
                    if result.retcode == mt5.TRADE_RETCODE_DONE:
                        profit_points = self.convert_to_points(result.profit, symbol) if hasattr(result, 'profit') else 0.0
                        position['profit'] = result.profit if hasattr(result, 'profit') else 0.0
                        
                        # Use a timeout context for the lock
                        if not self.command_lock.acquire(timeout=5):
                            self.logger.error(f"[{symbol}] Failed to acquire lock for closing ticket {ticket}")
                            return False
                        
                        try:
                            self.daily_profit[symbol] += position['profit']
                            self.update_trade_history_on_close(ticket, symbol, profit_points, reason)
                            del self.positions[symbol][ticket]
                        finally:
                            self.command_lock.release()
                        
                        df = self.get_or_update_rates(symbol, timeframe)
                        chart_path = self.generate_chart(df, "Exit", timeframe, symbol, position=position)
                        self.send_telegram_message(
                            f"[{symbol}] Closed ticket {ticket}: Profit={profit_points:.2f} points, Reason={reason}",
                            position['thread_id'],
                            chart_path
                        )
                        return True
                    
                    # Handle specific error codes
                    if result.retcode == 10013:  # Position already closed
                        self.logger.info(f"[{symbol}] Position {ticket} appears to be already closed")
                        # Use a timeout context for the lock
                        if self.command_lock.acquire(timeout=5):
                            try:
                                if ticket in self.positions[symbol]:
                                    del self.positions[symbol][ticket]
                            finally:
                                self.command_lock.release()
                        return True
                    
                    self.logger.error(f"[{symbol}] Failed to close ticket {ticket}: {result.comment} (retcode: {result.retcode})")
                    time.sleep(1)
                
                return False
                
        except Exception as e:
            self.logger.error(f"[{symbol}] Error closing ticket {ticket}: {str(e)}")
            # If position doesn't exist in MT5, remove it from local state
            if "position not found" in str(e).lower():
                # Use a timeout context for the lock
                if self.command_lock.acquire(timeout=5):
                    try:
                        if ticket in self.positions[symbol]:
                            del self.positions[symbol][ticket]
                    finally:
                        self.command_lock.release()
                return True
            return False
        
    def close_position_by_ticket(self, ticket):
        """Close a position by ticket number."""
        try:
            ticket = int(ticket)
            for symbol in self.symbols:
                if ticket in self.positions[symbol]:
                    position = self.positions[symbol][ticket]
                    return self.close_position(position, "Manual close from terminal")
            return f"Position with ticket {ticket} not found"
        except Exception as e:
            self.logger.error(f"Error closing position {ticket}: {str(e)}")
            return f"Error: {str(e)}"

    def generate_chart(self, df, signal_type, timeframe, symbol, position=None, entry_price=None, exit_price=None):
        fig = go.Figure()
        fig.add_trace(go.Candlestick(x=df['time'], open=df['open'], high=df['high'], low=df['low'], close=df['close'], name='OHLC'))
        fig.add_trace(go.Scatter(x=df['time'], y=df['ma_fast'], mode='lines', name=f'MA {self.ma_configs[timeframe]["fast"]}', line=dict(color='blue')))
        fig.add_trace(go.Scatter(x=df['time'], y=df['ma_slow'], mode='lines', name=f'MA {self.ma_configs[timeframe]["slow"]}', line=dict(color='red')))
        if position:
            fig.add_hline(y=position['entry_price'], line_dash="dash", line_color="blue", annotation_text="Entry")
            current_price = df['close'].iloc[-1]
            exit_price = current_price if signal_type == "Exit" else position.get('exit_price', current_price)
            fig.add_hline(y=exit_price, line_dash="dash", line_color="red", annotation_text="Exit")
            profit_points = self.convert_to_points(position['profit'], symbol)
            fig.add_annotation(x=df['time'].iloc[-1], y=exit_price, text=f"Profit: {profit_points:.2f} points", showarrow=True, arrowhead=1)
        elif entry_price:
            fig.add_hline(y=entry_price, line_dash="dash", line_color="blue", annotation_text="Entry")
        if exit_price and not position:
            fig.add_hline(y=exit_price, line_dash="dash", line_color="red", annotation_text="Exit")
        daily_profit = sum(self.daily_profit[s] for s in self.symbols)
        fig.add_annotation(x=0.95, y=0.95, xref="paper", yref="paper", text=f"Daily Target: {self.convert_to_points(daily_profit, symbol):.2f}/{self.daily_max_profit:.2f} points", showarrow=False)
        fig.update_layout(title=f'{symbol} {self.get_timeframe_name(timeframe)} {signal_type} Chart', yaxis_title='Price', xaxis_title='Time')
        filename = f"chart_{symbol}_{self.get_timeframe_name(timeframe)}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.png"
        fig.write_image(filename)
        return filename

    def prompt_trade_confirmation(self, symbol, timeframe, order_type, message, signal_time):
        """Send trade confirmation request to both Telegram and Terminal."""
        if not self.waiting_for_trade_confirmation[symbol][timeframe]:
            self.waiting_for_trade_confirmation[symbol][timeframe] = True
            confirmation_message = (
                f"🔔 Trade Confirmation Required:\n"
                f"{message}\n"
                f"Symbol: {symbol}\n"
                f"Timeframe: {self.get_timeframe_name(timeframe)}\n"
                f"Type: {order_type}\n"
                f"Reply 'yes' to confirm or 'no' to cancel."
            )
            
            # Send to Telegram
            thread_id = self.send_telegram_message(confirmation_message)
            
            # Send to Terminal
            print(f"\n{confirmation_message}")
            
            # Store confirmation details
            confirmation_details = {
                'symbol': symbol,
                'timeframe': timeframe,
                'order_type': order_type,
                'signal_time': signal_time,
                'thread_id': thread_id,
                'message': message,
                'timestamp': datetime.now()
            }
            
            # Store in queue for both Telegram and Terminal handlers
            self.trade_confirmation_queue.put(confirmation_details)
            
            # Log the confirmation request
            self.logger.info(f"[{symbol}] Trade confirmation requested for {order_type} on {self.get_timeframe_name(timeframe)}")

    def handle_trade_confirmation(self, text, message_id=None, source="telegram"):
        """Handle trade confirmation from both Telegram and Terminal."""
        text = text.lower().strip()
        if text not in ['yes', 'no']:
            return "Invalid response. Please reply with 'yes' or 'no'."

        try:
            # Get confirmation details without removing from queue
            confirmation_details = self.trade_confirmation_queue.queue[0]
            
            # For Telegram, verify message_id matches
            if source == "telegram" and message_id != confirmation_details['thread_id']:
                return
            
            # Remove from queue after verification
            confirmation_details = self.trade_confirmation_queue.get_nowait()
            
            symbol = confirmation_details['symbol']
            timeframe = confirmation_details['timeframe']
            order_type = confirmation_details['order_type']
            signal_time = confirmation_details['signal_time']
            thread_id = confirmation_details['thread_id']
            message = confirmation_details['message']
            
            if text == 'yes':
                tick = mt5.symbol_info_tick(symbol) if not self.simulate else None
                entry_price = tick.ask if order_type == "BUY" else tick.bid if tick else random.uniform(1000, 2000)
                success, position = self.open_position(
                    mt5.ORDER_TYPE_BUY if order_type == "BUY" else mt5.ORDER_TYPE_SELL,
                    entry_price, signal_time, message, timeframe, symbol
                )
                
                response = ""
                if success:
                    self.last_signal_times[symbol][timeframe] = datetime.now()
                    response = f"✅ Trade confirmed and opened: Ticket {position['ticket']}"
                    # Send confirmation to both interfaces
                    self.send_telegram_message(response, thread_id)
                    print(response)
                else:
                    response = "❌ Failed to open trade."
                    self.send_telegram_message(response, thread_id)
                    print(response)
            else:
                response = "❌ Trade cancelled."
                self.send_telegram_message(response, thread_id)
                print(response)
            
            self.waiting_for_trade_confirmation[symbol][timeframe] = False
            return response
            
        except queue.Empty:
            return "No pending trade confirmations."
        except Exception as e:
            self.logger.error(f"Error handling trade confirmation: {str(e)}")
            return f"Error handling trade confirmation: {str(e)}"

    def terminal_listener(self):
        """Handle terminal commands."""
        self.logger.info("Starting terminal listener...")
        session = PromptSession(history=InMemoryHistory())
        completer = WordCompleter([
            # Existing commands
            'help', 'exit', 'status', 'metrics', 'close_all', 'stop', 'start', 'resume', 'cd', 
            'add_account', 'switch_account', 'enable_sync', 'disable_sync', 'list_accounts', 
            'close', 'close_partial', 'add_to_position', 'buy_market', 'sell_market',
            'status', 'open', 'close', 'modify', 'history', 'chart', 'account', 'sync',
            'lock', 'unlock', 'report', 'mock', 'mockstatus', 'mockclose', 'optimize_signals',
            'disable_optimization', 'set_signal_interval', 'signal_stats', 'exit',
            # Timeframe-based commands
            'm1b', 'm5b', 'm15b', 'm30b', 'h1b', 'h4b',
            'm1s', 'm5s', 'm15s', 'm30s', 'h1s', 'h4s',
            'm1b0', 'm5b0', 'm15b0', 'm30b0', 'h1b0', 'h4b0',
            'm1s0', 'm5s0', 'm15s0', 'm30s0', 'h1s0', 'h4s0',
            
            # TP-based commands
            '50b', '100b', '150b', '200b', '250b', '300b', '350b', '400b', '500b', '600b', '800b', '1000b', '2000b',
            '50s', '100s', '150s', '200s', '250s', '300s', '350s', '400s', '500s', '600s', '800s', '1000s', '2000s',
            
            # Position management
            'set_sl', 'set_tp', 'modify', 'comment', 'reason', 'history', 'daily_history',
            'fetch_suretrend_history', 'set_lot_size', 'set_daily_profit_limit', 'set_breakeven',
            'set_trailing_stop', 'set_trailing_delay', 'set_cooldown',
            
            # MA exit commands
            'm1_exit', 'm5_exit', 'm15_exit', 'm30_exit', 'h1_exit', 'h4_exit',
            
            # Strategy control commands
            'enable_volatility', 'disable_volatility',
            'enable_psar_filter', 'disable_psar_filter',
            'enable_dynamic_management', 'disable_dynamic_management',
            'enable_suretrend_automation', 'disable_suretrend_automation',
            'enable_grid_trading', 'disable_grid_trading',
            'enable_primary_strategy', 'disable_primary_strategy',
            'enable_exit_signals', 'disable_exit_signals',
            
            # MA configuration
            'config_ma', 'config_ma_bulk',
            
            # Trade confirmation
            'yes', 'no',
            
            # Report generation
            'gen_report', '--ticket', '--symbol', '--daily',
            
            # Chart commands
            'fetch_chart',
            
            # New parameter setting command
            'setparams',
            
            # Semi-auto mode commands
            'enable_primary_semi_auto', 'disable_primary_semi_auto',
            'enable_suretrend_semi_auto', 'disable_suretrend_semi_auto',
            'enable_grid_semi_auto', 'disable_grid_semi_auto',
            'enable_momentum_semi_auto', 'disable_momentum_semi_auto',
            
            # Signal optimization commands
            'optimize_signals', 'disable_signal_optimization',
            'set_signal_interval', 'get_signal_stats',
            'enable_realtime_signals', 'disable_realtime_signals',
            'set_signal_threshold', 'reset_signal_stats',
            'show_signal_performance', 'export_signals',
            'enable_signal_alerts', 'disable_signal_alerts',
            'set_signal_filters', 'reset_signal_filters',
            'show_active_signals', 'clear_signal_history',
            'enable_signal_logging', 'disable_signal_logging',
            'set_signal_quality', 'get_signal_quality',
            'optimize_timeframes', 'reset_timeframes',
            'show_signal_distribution', 'export_signal_stats',
            
            # HFScalper commands
            'enable_hfscalper', 'disable_hfscalper',
            'enable_hfscalper_semi_auto', 'disable_hfscalper_semi_auto',
            'enable_hfscalper_psar', 'disable_hfscalper_psar',
            'set_hfscalper_min_momentum', 'set_hfscalper_volatility',
            'set_hfscalper_tp', 'set_hfscalper_psar_step',
            'set_hfscalper_psar_max', 'show_hfscalper_stats',
            
            # Strategy performance commands
            'show_strategy_stats', 'optimize_strategy',
            'reset_strategy_stats', 'export_strategy_stats',
            'enable_strategy_alerts', 'disable_strategy_alerts',
            'set_strategy_filters', 'reset_strategy_filters',
            
            # Performance monitoring commands
            'show_performance', 'export_performance',
            'reset_performance_stats', 'set_performance_alerts',
            'optimize_performance', 'show_performance_metrics'
        ], ignore_case=True)

        while True:
            try:
                command = session.prompt('> ', completer=completer)
                if command.lower() == 'exit':
                    self.cleanup()
                    os._exit(0)
                    
                # Check if this is a trade confirmation response
                if command.lower() in ['yes', 'no']:
                    response = self.handle_trade_confirmation(command.lower(), source="terminal")
                    print(response)
                    continue
                    
                # Handle regular commands
                response = self.handle_terminal_command(command)
                print(response)
            except KeyboardInterrupt:
                self.cleanup()
                os._exit(0)
            except Exception as e:
                self.logger.error(f"Terminal listener error: {e}")  

    def process_terminal_command(self, command):
        """Process terminal commands with enhanced command handling."""
        try:
            parts = command.strip().split()
            if not parts:
                return "No command provided"
            
            cmd = parts[0].lower()
            args = parts[1:]
                # Add new SureTrend monitoring commands
            if cmd == "start_suretrend_monitor":
                return self.start_suretrend_monitoring()
                
            if cmd == "stop_suretrend_monitor":
                return self.stop_suretrend_monitoring()
                
            if cmd == "show_suretrend":
                if len(cmd_parts) > 1:
                    symbol = cmd_parts[1].upper()
                    timeframe = None
                    if len(cmd_parts) > 2:
                        timeframe = self.parse_timeframe(cmd_parts[2])
                    return self.display_suretrend_checklist(symbol, timeframe)
                else:
                    return self.display_suretrend_checklist()
            
            command_map = {
                'status': self.display_trade_metrics,
                'open': lambda: self.open_trade(*args) if len(args) >= 3 else "Usage: open <symbol> <type> <timeframe>",
                'close': lambda: self.close_position_by_ticket(args[0]) if args else "Usage: close <ticket>",
                'modify': lambda: self.handle_position_params(['setparams'] + args) if len(args) >= 6 else "Usage: modify <ticket> <sl_points> <tp_points> <trail_stop> <trail_delay> <ma_exit>",
                'history': lambda: self.get_trade_history(args[0] if args else None),
                'chart': lambda: self.fetch_chart(args[0], args[1]) if len(args) == 2 else "Usage: chart <symbol> <timeframe>",
                'account': lambda: self.handle_account_command(args) if args else "Usage: account <add/switch> <name> [login] [password] [server]",
                'sync': lambda: "Sync initiated" if self.sync_with_mt5() else "Sync failed",
                'lock': lambda: self.lock_trading("Manual lock from terminal"),
                'unlock': lambda: self.unlock_trading(args[0]) if args else "Usage: unlock <admin_password>",
                'report': lambda: self.generate_trade_report(ticket=int(args[0]) if args else None, symbol=args[1] if len(args) > 1 else None),
                'mock': lambda: self.mock_trade(args[0], args[1], args[2], float(args[3]) if len(args) > 3 else 0.01) if len(args) >= 3 else "Usage: mock <symbol> <type> <timeframe> [lot_size]",
                'mockstatus': lambda: self.mock_trade_manager.get_mock_trade_info(int(args[0]) if args else None),
                'mockclose': lambda: self.mock_trade_manager.close_mock_trade(int(args[0]), args[1] if len(args) > 1 else "Manual close") if args else "Usage: mockclose <ticket> [reason]",
                'optimize_signals': self.optimize_signals,
                'disable_optimization': self.disable_signal_optimization,
                'set_signal_interval': lambda: self.set_signal_interval(args[0]) if args else "Usage: set_signal_interval <interval>",
                'signal_stats': lambda: self.get_signal_stats(args[0] if args else None, self.parse_timeframe(args[1]) if len(args) > 1 else None),
                'exit': lambda: self.handle_exit(None) or "Exiting..."
            }
            
            if cmd in command_map:
                result = command_map[cmd]()
                return str(result) if result is not None else "Command executed"
            return f"Unknown command: {cmd}"
            
        except Exception as e:
            self.logger.error(f"Error processing command '{command}': {str(e)}")
            return f"Error: {str(e)}"

    def telegram_listener(self):
        self.logger.info("Starting Telegram listener...")
        while True:
            try:
                updates = self.get_telegram_updates()
                if not updates or 'result' not in updates:
                    time.sleep(1)
                    continue
                for update in updates['result']:
                    if 'message' not in update or 'text' not in update['message']:
                        continue
                    message = update['message']
                    chat_id = message['chat']['id']
                    text = message['text'].strip()
                    message_id = message['message_id']
                    if chat_id != int(self.TELEGRAM_CHAT_ID):
                        self.send_telegram_message("Unauthorized chat ID.", chat_id=chat_id)
                        continue
                    if text.startswith('/'):
                        command = text[1:]
                        response = self.handle_telegram_command(command)
                        self.send_telegram_message(response, chat_id=chat_id, thread_id=message_id)
                    else:
                        self.handle_trade_confirmation(text, message_id)
            except Exception as e:
                self.logger.error(f"Telegram listener error: {e}")
                time.sleep(5)

    def handle_telegram_command(self, command):
        # First ensure we're synced with MT5
        if not self.simulate:
            self.sync_positions_with_mt5()

        cmd_parts = command.lower().split()
        if not cmd_parts:
            return "🤔 Empty command received. Type 'help' for available commands."

        cmd = cmd_parts[0]

        if cmd == "unlock_trading" and len(cmd_parts) >= 2:
            password = cmd_parts[1]
            return self.unlock_trading(password)

        if cmd == "trading_status":
            if self.trading_locked:
                return f"🔒 Trading is currently locked\nReason: {self.trading_lock_reason}"
            return "✅ Trading is active"

        if cmd == "gen_report":
            try:
                if len(cmd_parts) < 2:
                    return "Usage: gen_report --ticket <ticket> | --symbol <symbol> | --daily"
                
                if cmd_parts[1] == "--ticket" and len(cmd_parts) >= 3:
                    return self.generate_trade_report(ticket=int(cmd_parts[2]))
                elif cmd_parts[1] == "--symbol" and len(cmd_parts) >= 3:
                    return self.generate_trade_report(symbol=cmd_parts[2].upper())
                elif cmd_parts[1] == "--daily":
                    return self.generate_trade_report(daily=True)
                else:
                    return "Invalid report type. Use --ticket, --symbol, or --daily"
            except Exception as e:
                return f"Error generating report: {str(e)}"
        scope = self.context_symbol or self.symbols
        if isinstance(scope, str):
            scope = [scope]

        # Add new pattern for immediate TP-based trades
        tp_immediate_match = re.match(r'(\d+)(b0|s0)$', cmd)
        if tp_immediate_match and len(cmd_parts) >= 2:
            tp_points = int(tp_immediate_match.group(1))
            direction = "BUY" if tp_immediate_match.group(2) == 'b0' else "SELL"
            symbol = cmd_parts[1].upper()
            timeframe = self.parse_timeframe(cmd_parts[2]) if len(cmd_parts) > 2 else mt5.TIMEFRAME_M1
            
            if symbol in self.symbols and timeframe:
                tick = mt5.symbol_info_tick(symbol)
                if not tick:
                    return f"Failed to fetch tick data for {symbol}."
                
                price = tick.ask if direction == "BUY" else tick.bid
                order_type = mt5.ORDER_TYPE_BUY if direction == "BUY" else mt5.ORDER_TYPE_SELL
                
                # Calculate TP based on points
                tp = price + (tp_points * self.point[symbol]) if direction == "BUY" else price - (tp_points * self.point[symbol])
                sl = price - (self.initial_sl * self.point[symbol]) if direction == "BUY" else price + (self.initial_sl * self.point[symbol])
                
                success, position = self.open_position(
                    order_type, price, datetime.now(),
                    f"Immediate {tp_points} points TP Trade on {symbol}\nDirection: {direction}",
                    timeframe, symbol
                )
                
                if success:
                    # Update TP for the position
                    self.modify_position(position, tp=tp)
                    return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {sl:.5f}\n✨ TP: {tp:.5f}"
                return f"Failed to open {direction} position on {symbol} with TP {tp_points} points."
            return f"Invalid symbol '{symbol}' or timeframe '{cmd_parts[2] if len(cmd_parts) > 2 else 'M1'}'. Available symbols: {', '.join(self.symbols)}"

        if cmd == "metrics":
            try:
                # Force sync with MT5 before calculating metrics
                if not self.simulate:
                    self.sync_positions_with_mt5()
                
                metrics_lines = [f"📊 Detailed Trading Metrics Report for Scope {', '.join(scope)}:"]
                
                # Get current account info
                account_info = mt5.account_info() if not self.simulate else None
                balance = account_info.balance if account_info else self.initial_balance
                equity = account_info.equity if account_info else balance
                
                metrics_lines.append(f"💰 Account Balance: ${balance:.2f}")
                metrics_lines.append(f"📈 Equity: ${equity:.2f}")
                
                total_positions = sum(len(self.positions[sym]) for sym in scope)
                metrics_lines.append(f"📌 Total Open Positions: {total_positions}")
                
                # Calculate total daily profit
                total_points = 0
                for sym in scope:
                    if not self.simulate:
                        # Get current market prices for accurate profit calculation
                        tick = mt5.symbol_info_tick(sym)
                        if tick:
                            # Update profits for all positions
                            for pos in self.positions[sym].values():
                                if pos['type'] == mt5.ORDER_TYPE_BUY:
                                    pos['profit'] = (tick.bid - pos['entry_price']) * pos['lot_size'] * 10000
                                else:
                                    pos['profit'] = (pos['entry_price'] - tick.ask) * pos['lot_size'] * 10000
                
                    total_points += self.convert_to_points(self.daily_profit[sym], sym)
                
                metrics_lines.append(f"💵 Total Daily Profit: {total_points:.2f} points")
                metrics_lines.append("")
                
                for symbol in scope:
                    metrics_lines.append(f"🔍 {symbol} Metrics:")
                    open_positions = len(self.positions[symbol])
                    metrics_lines.append(f"  📊 Open Positions: {open_positions}")
                    
                    if open_positions > 0:
                        # Get current market prices
                        tick = mt5.symbol_info_tick(symbol) if not self.simulate else None
                        
                        for pos in self.positions[symbol].values():
                            # Verify position still exists in MT5
                            mt5_position = None if self.simulate else mt5.positions_get(ticket=pos['ticket'])
                            
                            if self.simulate or mt5_position:
                                current_profit = pos['profit']
                                if not self.simulate and tick:
                                    # Calculate real-time profit
                                    if pos['type'] == mt5.ORDER_TYPE_BUY:
                                        current_profit = (tick.bid - pos['entry_price']) * pos['lot_size'] * 10000
                                    else:
                                        current_profit = (pos['entry_price'] - tick.ask) * pos['lot_size'] * 10000
                                
                                profit_points = self.convert_to_points(current_profit, symbol)
                                
                                metrics_lines.append(
                                    f"    🎫 Ticket {pos['ticket']}: {pos['lot_size']} lots\n"
                                    f"       💰 Entry: {pos['entry_price']:.5f}\n"
                                    f"       🛑 SL: {pos['sl']:.5f}\n"
                                    f"       ✨ TP: {pos['tp']:.5f}\n"
                                    f"       📈 Current Profit: {profit_points:.2f} points\n"
                                    f"       📋 Strategy: {pos['strategy']}"
                                )
                    
                    daily_profit_points = self.convert_to_points(self.daily_profit[symbol], symbol)
                    metrics_lines.append(f"  💵 Daily Profit: {daily_profit_points:.2f} points")
                    metrics_lines.append(f"  📊 Total Trades Today: {len(self.daily_trades[symbol])}")
                
                return "\n".join(metrics_lines) if total_positions > 0 else f"No open positions in scope {', '.join(scope)}."
                
            except Exception as e:
                self.logger.error(f"Error generating metrics: {str(e)}")
                return f"Error generating metrics: {str(e)}"

        if cmd == "cd":
            if len(cmd_parts) >= 2:
                if cmd_parts[1] == "..":
                    self.context_symbol = None
                    return "📍 Context set to all symbols. All commands will now apply to all symbols."
                symbol = cmd_parts[1].upper()
                if symbol in self.symbols:
                    self.context_symbol = symbol
                    return f"📍 Context set to {symbol}. All commands will now apply to {symbol} only."
                return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"
            return "Usage: cd <symbol> | .."

        if cmd == "add_account" and len(cmd_parts) == 5:
            name, login, password, server = cmd_parts[1], cmd_parts[2], cmd_parts[3], cmd_parts[4]
            if self.add_account(name, login, password, server):
                return f"✅ Account '{name}' added successfully!\n🏦 Server: {server}\n🔑 Login: {login}"
            return f"Failed to add account '{name}'."
    
        if cmd == "switch_account" and len(cmd_parts) == 2:
            name = cmd_parts[1]
            if self.switch_account(name):
                return f"Switched to account '{name}'."
            return f"Failed to switch to account '{name}'."
    
        if cmd == "enable_sync":
            self.sync_enabled = True
            return "Account synchronization enabled."
    
        if cmd == "disable_sync":
            self.sync_enabled = False
            return "Account synchronization disabled."
    
        if cmd == "list_accounts":
            if not self.accounts:
                return "No trading accounts configured"
            account_info = []
            for name, details in self.accounts.items():
                status = "Active" if name == self.current_account else "Inactive"
                account_info.append(f"{name}: {details['server']} ({status})")
            return "Trading Accounts:\n" + "\n".join(account_info)

        if cmd == "stop":
            for symbol in scope:
                self.trading_allowed[symbol] = False
            return f"Trading stopped for {', '.join(scope)}."

        if cmd == "start":
            for symbol in scope:
                self.trading_allowed[symbol] = True
            return f"Trading started for {', '.join(scope)}."

        if cmd == "resume" and len(cmd_parts) >= 2:
            symbol = cmd_parts[1].upper()
            if symbol in self.symbols:
                self.trading_allowed[symbol] = True
                return f"Trading resumed for {symbol}."
            return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"

        def close_position_task(position):
            nonlocal closed, failed
            try:
                success = self.close_position(position, "Manual close_all")
                if success:
                    closed += 1
                else:
                    failed += 1
            except Exception as e:
                self.logger.error(f"Error closing position {position['ticket']}: {str(e)}")
                failed += 1

        if cmd == "close_all":
            closed = 0
            failed = 0
            try:
                with ThreadPoolExecutor() as executor:
                    futures = []
                    for symbol in scope:
                        positions_to_close = list(self.positions[symbol].values())
                        for position in positions_to_close:
                            futures.append(executor.submit(close_position_task, position))

                    # Wait for all tasks to complete
                    for future in futures:
                        future.result()

                if closed > 0:
                    return f"✅ Successfully closed {closed} positions" + (f", {failed} failed" if failed > 0 else "")
                elif failed > 0:
                    return f"❌ Failed to close {failed} positions"
                return "No open positions to close"
                
            except Exception as e:
                self.logger.error(f"Error in close_all command: {str(e)}")
                return f"Error executing close_all command: {str(e)}"

        if cmd == "close" and len(cmd_parts) >= 2:
            ticket = int(cmd_parts[1])
            for symbol in scope:
                if ticket in self.positions[symbol]:
                    success = self.close_position(self.positions[symbol][ticket], "Manual close")
                    return f"Position {ticket} closed successfully for {symbol}." if success else f"Failed to close position {ticket} for {symbol}."
            return f"Position with ticket {ticket} not found in scope {', '.join(scope)}."

        if cmd == "close_partial" and len(cmd_parts) >= 4:
            symbol = cmd_parts[1].upper()
            ticket = int(cmd_parts[2])
            pct = float(cmd_parts[3])
            if symbol in self.symbols and ticket in self.positions[symbol]:
                position = self.positions[symbol][ticket]
                partial_lot = position['lot_size'] * (pct / 100)
                if self.simulate:
                    current_price = random.uniform(position['entry_price'] - 50 * self.point[symbol], position['entry_price'] + 50 * self.point[symbol])
                    profit_points = self.convert_to_points(
                        (current_price - position['entry_price']) * partial_lot * 10000 if position['type'] == mt5.ORDER_TYPE_BUY else
                        (position['entry_price'] - current_price) * partial_lot * 10000, symbol)
                    position['lot_size'] -= partial_lot
                    if position['lot_size'] <= 0:
                        del self.positions[symbol][ticket]
                        return f"Partially closed ticket {ticket} for {symbol}: {pct}% ({partial_lot:.2f} lots), Simulated Profit: {profit_points:.2f} points. Position fully closed."
                    self.daily_profit[symbol] += profit_points * self.point[symbol] * partial_lot * 10000
                    return f"Partially closed ticket {ticket} for {symbol}: {pct}% ({partial_lot:.2f} lots), Simulated Profit: {profit_points:.2f} points. Remaining lots: {position['lot_size']:.2f}."
                else:
                    request = {
                        "action": mt5.TRADE_ACTION_DEAL,
                        "symbol": symbol,
                        "volume": partial_lot,
                        "type": mt5.ORDER_TYPE_SELL if position['type'] == mt5.ORDER_TYPE_BUY else mt5.ORDER_TYPE_BUY,
                        "position": ticket,
                        "price": mt5.symbol_info_tick(symbol).bid if position['type'] == mt5.ORDER_TYPE_BUY else mt5.symbol_info_tick(symbol).ask,
                        "deviation": self.deviation,
                        "magic": 234000,
                        "comment": "Partial close",
                        "type_time": mt5.ORDER_TIME_GTC,
                        "type_filling": mt5.ORDER_FILLING_IOC
                    }
                    result = mt5.order_send(request)
                    if result.retcode == mt5.TRADE_RETCODE_DONE:
                        position['lot_size'] -= partial_lot
                        profit_points = self.convert_to_points(result.profit, symbol) if hasattr(result, 'profit') else 0
                        self.daily_profit[symbol] += profit_points * self.point[symbol] * partial_lot * 10000
                        if position['lot_size'] <= 0:
                            del self.positions[symbol][ticket]
                            return f"Partially closed ticket {ticket} for {symbol}: {pct}% ({partial_lot:.2f} lots), Profit: {profit_points:.2f} points. Position fully closed."
                        return f"Partially closed ticket {ticket} for {symbol}: {pct}% ({partial_lot:.2f} lots), Profit: {profit_points:.2f} points. Remaining lots: {position['lot_size']:.2f}."
                    return f"Failed to partially close ticket {ticket} for {symbol}: {result.comment}"
            return f"Invalid symbol '{symbol}' or ticket {ticket} not found."

        if cmd == "add_to_position" and len(cmd_parts) >= 4:
            symbol = cmd_parts[1].upper()
            ticket = int(cmd_parts[2])
            lot = float(cmd_parts[3])
            if symbol in self.symbols and ticket in self.positions[symbol]:
                position = self.positions[symbol][ticket]
                if self.simulate:
                    position['lot_size'] += lot
                    return f"Simulated addition of {lot:.2f} lots to ticket {ticket} for {symbol}. New lot size: {position['lot_size']:.2f}."
                else:
                    request = {
                        "action": mt5.TRADE_ACTION_DEAL,
                        "symbol": symbol,
                        "volume": lot,
                        "type": position['type'],
                        "price": mt5.symbol_info_tick(symbol).ask if position['type'] == mt5.ORDER_TYPE_BUY else mt5.symbol_info_tick(symbol).bid,
                        "deviation": self.deviation,
                        "magic": 234000,
                        "comment": "Add to position",
                        "type_time": mt5.ORDER_TIME_GTC,
                        "type_filling": mt5.ORDER_FILLING_IOC
                    }
                    result = mt5.order_send(request)
                    if result.retcode == mt5.TRADE_RETCODE_DONE:
                        position['lot_size'] += lot
                        return f"Added {lot:.2f} lots to ticket {ticket} for {symbol}. New lot size: {position['lot_size']:.2f}."
                    return f"Failed to add {lot:.2f} lots to ticket {ticket} for {symbol}: {result.comment}"
            return f"Invalid symbol '{symbol}' or ticket {ticket} not found."

        if cmd == "buy_market" and len(cmd_parts) >= 3:
            timeframe = self.parse_timeframe(cmd_parts[1])
            symbol = cmd_parts[2].upper()
            if timeframe and symbol in self.symbols:
                tick = mt5.symbol_info_tick(symbol)
                if not tick:
                    return f"Failed to fetch tick data for {symbol}."
                price = tick.ask
                success, position = self.open_position(mt5.ORDER_TYPE_BUY, price, datetime.now(),
                                                      f"Manual BUY via Terminal on {self.get_timeframe_name(timeframe)} at {price:.2f}",
                                                      timeframe, symbol)
                return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {position['sl']:.5f}\n✨ TP: {position['tp']:.5f}" if success else \
                       f"Failed to place market buy order for {symbol}."
            return f"Invalid timeframe '{cmd_parts[1]}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "sell_market" and len(cmd_parts) >= 3:
            timeframe = self.parse_timeframe(cmd_parts[1])
            symbol = cmd_parts[2].upper()
            if timeframe and symbol in self.symbols:
                tick = mt5.symbol_info_tick(symbol)
                if not tick:
                    return f"Failed to fetch tick data for {symbol}."
                price = tick.bid
                success, position = self.open_position(mt5.ORDER_TYPE_SELL, price, datetime.now(),
                                                      f"Manual SELL via Terminal on {self.get_timeframe_name(timeframe)} at {price:.2f}",
                                                      timeframe, symbol)
                return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {position['sl']:.5f}\n✨ TP: {position['tp']:.5f}" if success else \
                       f"Failed to place market sell order for {symbol}."
            return f"Invalid timeframe '{cmd_parts[1]}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd in ["m1b", "m5b", "m15b", "m30b", "h1b", "h4b", "m1s", "m5s", "m15s", "m30s", "h1s", "h4s"] and len(cmd_parts) >= 2:
            tf = cmd[:2].upper()
            direction = cmd[2].upper()
            symbol = cmd_parts[1].upper()
            if tf in self.timeframe_configs and symbol in self.symbols:
                timeframe = self.timeframe_configs[tf]
                conditions_met, message = self.check_manual_trade_conditions(symbol, timeframe, "BUY" if direction == "B" else "SELL")
                if not conditions_met:
                    return f"Cannot place {direction} trade on {symbol} {tf}: {message}"
                order_type = mt5.ORDER_TYPE_BUY if direction == "B" else mt5.ORDER_TYPE_SELL
                tick = mt5.symbol_info_tick(symbol)
                if not tick:
                    return f"Failed to fetch tick data for {symbol}."
                price = tick.ask if direction == "B" else tick.bid
                success, position = self.open_position(order_type, price, datetime.now(),
                                                      f"{tf} {direction} Manual Trade on {symbol}\nConditions: {message}",
                                                      timeframe, symbol)
                return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {position['sl']:.5f}\n✨ TP: {position['tp']:.5f}" if success else \
                       f"Failed to open {direction} position on {symbol} {tf}."
            return f"Invalid timeframe '{tf}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd in ["50b", "100b", "150b", "200b", "250b", "300b", "350b", "400b", "500b", "600b", "800b", "1000b", "2000b",
                   "50s", "100s", "150s", "200s", "250s", "300s", "350s", "400s", "500s", "600s", "800s", "1000s", "2000s"] and len(cmd_parts) >= 3:
            tp_points = int(cmd[:-1])
            direction = cmd[-1].upper()
            symbol = cmd_parts[1].upper()
            timeframe = self.parse_timeframe(cmd_parts[2]) if len(cmd_parts) > 2 else mt5.TIMEFRAME_M1
            if symbol in self.symbols and timeframe:
                conditions_met, message = self.check_manual_trade_conditions(symbol, timeframe, "BUY" if direction == "B" else "SELL")
                if not conditions_met:
                    return f"Cannot place {direction} trade with TP {tp_points} on {symbol}: {message}"
                tick = mt5.symbol_info_tick(symbol)
                if not tick:
                    return f"Failed to fetch tick data for {symbol}."
                price = tick.ask if direction == "B" else tick.bid
                order_type = mt5.ORDER_TYPE_BUY if direction == "B" else mt5.ORDER_TYPE_SELL
                sl = price - (self.initial_sl * self.point[symbol]) if order_type == mt5.ORDER_TYPE_BUY else price + (self.initial_sl * self.point[symbol])
                success, position = self.open_position(order_type, price, datetime.now(),
                                                      f"{tp_points}{direction} MA TP Trade on {symbol}\nConditions: {message}",
                                                      timeframe, symbol)
                if success:
                    self.positions[symbol][position['ticket']]['ma_tp_timeframe'] = timeframe
                    return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {sl:.2f}\n✨ TP: {position['tp']:.2f}"
                return f"Failed to open {direction} position on {symbol} with TP {tp_points} points."
            return f"Invalid symbol '{symbol}' or timeframe '{cmd_parts[2] if len(cmd_parts) > 2 else 'M1'}'. Available symbols: {', '.join(self.symbols)}"

        if cmd in ["m1b0", "m5b0", "m15b0", "m30b0", "h1b0", "h4b0", "m1s0", "m5s0", "m15s0", "m30s0", "h1s0", "h4s0"] and len(cmd_parts) >= 2:
            tf = cmd[:2].upper()
            direction = cmd[2].upper()
            symbol = cmd_parts[1].upper()
            if tf in self.timeframe_configs and symbol in self.symbols:
                timeframe = self.timeframe_configs[tf]
                order_type = mt5.ORDER_TYPE_BUY if direction == "B" else mt5.ORDER_TYPE_SELL
                tick = mt5.symbol_info_tick(symbol) if not self.simulate else None
                price = tick.ask if direction == "B" else tick.bid if tick else random.uniform(1000, 2000)
                success, position = self.open_position(order_type, price, datetime.now(),
                                                      f"{tf} {direction} Immediate Manual Trade on {symbol}",
                                                      timeframe, symbol)
                return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {position['sl']:.5f}\n✨ TP: {position['tp']:.5f}" if success else \
                       f"Failed to open {direction} position on {symbol} {tf}."
            return f"Invalid timeframe '{tf}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "set_sl" and len(cmd_parts) >= 4:
            symbol = cmd_parts[1].upper()
            ticket = int(cmd_parts[2])
            value = float(cmd_parts[3])
            if symbol in self.symbols and ticket in self.positions[symbol]:
                self.modify_position(self.positions[symbol][ticket], sl=value)
                return f"Stop Loss set to {value:.2f} for ticket {ticket} on {symbol}."
            return f"Invalid symbol '{symbol}' or ticket {ticket} not found."

        if cmd == "set_tp" and len(cmd_parts) >= 4:
            symbol = cmd_parts[1].upper()
            ticket = int(cmd_parts[2])
            value = float(cmd_parts[3])
            if symbol in self.symbols and ticket in self.positions[symbol]:
                self.modify_position(self.positions[symbol][ticket], tp=value)
                return f"Take Profit set to {value:.2f} for ticket {ticket} on {symbol}."
            return f"Invalid symbol '{symbol}' or ticket {ticket} not found."

        if cmd == "modify" and len(cmd_parts) >= 5:
            symbol = cmd_parts[1].upper()
            ticket = int(cmd_parts[2])
            param = cmd_parts[3].lower()
            value = float(cmd_parts[4])
            if symbol in self.symbols and ticket in self.positions[symbol]:
                if param == "sl":
                    self.modify_position(self.positions[symbol][ticket], sl=value)
                    return f"Stop Loss modified to {value:.2f} for ticket {ticket} on {symbol}."
                elif param == "tp":
                    self.modify_position(self.positions[symbol][ticket], tp=value)
                    return f"Take Profit modified to {value:.2f} for ticket {ticket} on {symbol}."
                return f"Invalid parameter '{param}'. Use 'sl' or 'tp'."
            return f"Invalid symbol '{symbol}' or ticket {ticket} not found."

        if cmd == "comment" and len(cmd_parts) >= 3:
            ticket = int(cmd_parts[1])
            text = " ".join(cmd_parts[2:])
            for symbol in scope:
                if ticket in self.positions[symbol]:
                    self.positions[symbol][ticket]['comments'] = text
                    return f"Comment '{text}' added to ticket {ticket} for {symbol}."
            return f"Ticket {ticket} not found in scope {', '.join(scope)}."

        if cmd == "reason" and len(cmd_parts) >= 3:
            ticket = int(cmd_parts[1])
            text = " ".join(cmd_parts[2:])
            for symbol in scope:
                if ticket in self.positions[symbol]:
                    self.positions[symbol][ticket]['reason'] = text
                    return f"Reason updated to '{text}' for ticket {ticket} on {symbol}."
            return f"Ticket {ticket} not found in scope {', '.join(scope)}."

        if cmd == "history":
            history_lines = [f"Recent Trade History for Scope {', '.join(scope)}:"]
            
            for symbol in scope:
                history_lines.append(f"{symbol}:")
                
                try:
                    # Get current open positions from MT5
                    positions = mt5.positions_get(symbol=symbol) if not self.simulate else []
                    open_trades = []
                    if positions:
                        for pos in positions:
                            try:
                                current_profit = getattr(pos, 'profit', 0.0)
                                profit_points = self.convert_to_points(current_profit, symbol)
                                
                                trade = {
                                    "ticket": getattr(pos, 'ticket', 0),
                                    "type": "BUY" if getattr(pos, 'type', 0) == mt5.ORDER_TYPE_BUY else "SELL",
                                    "profit": current_profit,
                                    "profit_points": profit_points,
                                    "timeframe": self.get_timeframe_name(mt5.TIMEFRAME_M1),  # Default to M1 for open positions
                                    "entry_time": datetime.fromtimestamp(getattr(pos, 'time', datetime.now().timestamp())).strftime('%Y-%m-%d %H:%M:%S'),
                                    "symbol": getattr(pos, 'symbol', symbol),
                                    "status": "open",
                                    "lot_size": getattr(pos, 'volume', 0.01),
                                    "entry_price": getattr(pos, 'price_open', 0.0),
                                    "sl": getattr(pos, 'sl', 0.0),
                                    "tp": getattr(pos, 'tp', 0.0),
                                    "commission": 0.0,  # Default values for commission and swap
                                    "swap": getattr(pos, 'swap', 0.0),
                                    "comment": getattr(pos, 'comment', '') or "MT5 Trade"
                                }
                                open_trades.append(trade)
                            except Exception as e:
                                self.logger.debug(f"Error processing position {getattr(pos, 'ticket', 'unknown')}: {str(e)}")
                                continue
                
                    # Get closed trades from MT5 history
                    closed_trades = self.get_mt5_history(symbol)
                    
                    # Combine and sort all trades
                    all_trades = open_trades + closed_trades
                    all_trades.sort(key=lambda x: datetime.strptime(x['entry_time'], '%Y-%m-%d %H:%M:%S'), reverse=True)
                    
                    if not all_trades:
                        history_lines.append("  No trades found.")
                    else:
                        for trade in all_trades[:5]:  # Show last 5 trades
                            try:
                                status_info = f"[{trade.get('status', 'UNKNOWN').upper()}]"
                                profit_info = f"Profit: {trade.get('profit_points', 0.0):.2f} points (${trade.get('profit', 0.0):.2f})"
                                commission_info = f", Commission: ${trade.get('commission', 0.0):.2f}" if trade.get('commission', 0.0) != 0 else ""
                                swap_info = f", Swap: ${trade.get('swap', 0.0):.2f}" if trade.get('swap', 0.0) != 0 else ""
                                
                                entry_info = f"Entry: {trade.get('entry_time', 'Unknown')} @ {trade.get('entry_price', 0.0):.5f}"
                                close_info = f", Closed: {trade.get('close_time', '')} @ {trade.get('close_price', 0.0):.5f}" if trade.get('close_time') else ""
                                sl_tp_info = (f", SL: {trade.get('sl', 0.0):.5f}, TP: {trade.get('tp', 0.0):.5f}" 
                                            if trade.get('sl') is not None and trade.get('tp') is not None else "")
                                
                                comment_info = f", Comment: {trade.get('comment', '')}" if trade.get('comment') else ""
                                
                                history_lines.append(
                                    f"  {trade.get('type', 'UNKNOWN')} Ticket {trade.get('ticket', 'Unknown')}: {status_info}\n"
                                    f"    {profit_info}{commission_info}{swap_info}\n"
                                    f"    {entry_info}{close_info}{sl_tp_info}{comment_info}\n"
                                    f"    Volume: {trade.get('lot_size', 0.01):.2f} lots"
                                )
                            except Exception as e:
                                self.logger.debug(f"Error formatting trade {trade.get('ticket', 'unknown')}: {str(e)}")
                                continue
                    
                except Exception as e:
                    self.logger.error(f"Error processing trade history for {symbol}: {str(e)}")
                    history_lines.append(f"  Error processing trade history: {str(e)}")
                
            return "\n".join(history_lines)

        if cmd == "daily_history" and len(cmd_parts) >= 2:
            symbol = cmd_parts[1].upper()
            if symbol in self.symbols:
                today_start = datetime.now().replace(hour=0, minute=0, second=0, microsecond=0)
                history_lines = [f"Daily Trade History for {symbol} ({today_start.date()}):"]
                all_trades = self.trade_history[symbol] + self.grid_history[symbol] + self.suretrend_history[symbol] + self.momentum_history[symbol]
                trades = [trade for trade in all_trades 
                         if 'entry_time' in trade and datetime.strptime(trade['entry_time'], '%Y-%m-%d %H:%M:%S.%f') >= today_start]
                if not trades:
                    history_lines.append("  No trades executed today.")
                for trade in sorted(trades, key=lambda x: datetime.strptime(x['entry_time'], '%Y-%m-%d %H:%M:%S.%f')):
                    profit_points = self.convert_to_points(trade['profit'], symbol)
                    history_lines.append(f"  {trade['type']} Ticket {trade['ticket']}: Profit {profit_points:.2f} points, "
                                        f"Entry Time: {trade['entry_time']}, Timeframe: {trade['timeframe']}")
                return "\n".join(history_lines)
            return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"

        if cmd == "fetch_suretrend_history" and len(cmd_parts) >= 2:
            symbol = cmd_parts[1].upper()
            if symbol in self.symbols:
                history_lines = [f"SureTrend Trade History for {symbol} (Last 5):"]
                trades = self.suretrend_history[symbol][-5:]
                if not trades:
                    history_lines.append("  No SureTrend trades recorded.")
                for trade in trades:
                    profit_points = self.convert_to_points(trade['profit'], symbol)
                    history_lines.append(f"  {trade['type']} Ticket {trade['ticket']}: Profit {profit_points:.2f} points, "
                                        f"Entry Time: {trade['entry_time']}, Timeframe: {trade['timeframe']}")
                return "\n".join(history_lines)
            return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"

        if cmd == "set_lot_size" and len(cmd_parts) >= 2:
            try:
                new_size = float(cmd_parts[1])
                if new_size <= 0:
                    return "Lot size must be positive."
                self.lot_size = new_size
                return f"Default lot size updated to {new_size:.2f}."
            except ValueError:
                return f"Invalid lot size '{cmd_parts[1]}'. Please provide a numeric value."

        if cmd == "set_daily_profit_limit" and len(cmd_parts) >= 2:
            new_limit = float(cmd_parts[1])
            self.daily_max_profit = new_limit
            return f"Daily profit limit set to {new_limit:.2f} points."

        if cmd == "set_breakeven" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            value = float(cmd_parts[2])
            if tf:
                self.breakeven_configs[tf] = value
                return f"Breakeven trigger set to {value:.2f} points for {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe: {cmd_parts[1]}. Available timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "set_trailing_stop" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            value = float(cmd_parts[2])
            if tf:
                self.trailing_stop_configs[tf] = value
                return f"Trailing stop distance set to {value:.2f} points for {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe: {cmd_parts[1]}. Available timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "set_trailing_delay" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            value = float(cmd_parts[2])
            if tf:
                self.trailing_delay_configs[tf] = value
                return f"Trailing stop activation delay set to {value:.2f} points for {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe: {cmd_parts[1]}. Available timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "set_cooldown" and len(cmd_parts) >= 2:
            new_cooldown = int(cmd_parts[1])
            self.signal_cooldown = new_cooldown
            return f"Signal cooldown set to {new_cooldown} seconds."

        if cmd in ["m1_exit", "m5_exit", "m15_exit", "m30_exit", "h1_exit", "h4_exit"] and len(cmd_parts) >= 3:
            tf_str = cmd.split('_')[0].upper()
            state = cmd_parts[1].lower()
            symbol = cmd_parts[2].upper()
            if tf_str in self.timeframe_configs and state in ["on", "off"] and symbol in self.symbols:
                timeframe = self.timeframe_configs[tf_str]
                self.ma_exit_enabled[symbol][timeframe] = state == "on"
                return f"{tf_str} exit signals {'enabled' if self.ma_exit_enabled[symbol][timeframe] else 'disabled'} for {symbol}."
            return f"Invalid timeframe '{tf_str}', state '{state}', or symbol '{symbol}'. Usage: {cmd} <on/off> <symbol>"

        if cmd == "enable_volatility" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            symbol = cmd_parts[2].upper()
            if tf and symbol in self.symbols:
                self.volatility_check_enabled[symbol][tf] = True
                return f"Volatility check enabled for {symbol} on {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe '{cmd_parts[1]}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "disable_volatility" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            symbol = cmd_parts[2].upper()
            if tf and symbol in self.symbols:
                self.volatility_check_enabled[symbol][tf] = False
                return f"Volatility check disabled for {symbol} on {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe '{cmd_parts[1]}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "enable_psar_filter" and len(cmd_parts) >= 4:
            mon_tf = self.parse_timeframe(cmd_parts[1])
            psar_tf = self.parse_timeframe(cmd_parts[2])
            symbol = cmd_parts[3].upper()
            if mon_tf and psar_tf and symbol in self.symbols:
                self.psar_filter_enabled[symbol][mon_tf] = True
                self.psar_filter_timeframe[symbol][mon_tf] = psar_tf
                return f"PSAR filter enabled for {symbol} on {self.get_timeframe_name(mon_tf)} using {self.get_timeframe_name(psar_tf)}."
            return f"Invalid monitoring timeframe '{cmd_parts[1]}' or PSAR timeframe '{cmd_parts[2]}' or symbol '{symbol}'."

        if cmd == "disable_psar_filter" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            symbol = cmd_parts[2].upper()
            if tf and symbol in self.symbols:
                self.psar_filter_enabled[symbol][tf] = False
                return f"PSAR filter disabled for {symbol} on {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe '{cmd_parts[1]}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "enable_dynamic_management":
            self.dynamic_management_enabled = True
            return f"Dynamic position management enabled for scope {', '.join(scope)}."

        if cmd == "disable_dynamic_management":
            self.dynamic_management_enabled = False
            return f"Dynamic position management disabled for scope {', '.join(scope)}."

        if cmd == "enable_suretrend_automation":
            self.suretrend_automation_enabled = True
            return f"SureTrend automation enabled for scope {', '.join(scope)}."

        if cmd == "disable_suretrend_automation":
            self.suretrend_automation_enabled = False
            return f"SureTrend automation disabled for scope {', '.join(scope)}."

        if cmd == "enable_grid_trading":
            self.grid_trading_enabled = True
            return f"Grid trading enabled for scope {', '.join(scope)}."

        if cmd == "disable_grid_trading":
            self.grid_trading_enabled = False
            return f"Grid trading disabled for scope {', '.join(scope)}."

        if cmd == "enable_primary_strategy":
            self.primary_strategy_enabled = True
            return f"Primary strategy enabled for scope {', '.join(scope)}."

        if cmd == "disable_primary_strategy":
            self.primary_strategy_enabled = False
            return f"Primary strategy disabled for scope {', '.join(scope)}."

        if cmd == "enable_exit_signals":
            self.exit_signals_enabled = True
            return f"Exit signals enabled for scope {', '.join(scope)}."

        if cmd == "disable_exit_signals":
            self.exit_signals_enabled = False
            return f"Exit signals disabled for scope {', '.join(scope)}."

        if cmd == "config_ma" and len(cmd_parts) >= 5:
            tf = self.parse_timeframe(cmd_parts[1])
            ma_type = cmd_parts[2].lower()
            period = int(cmd_parts[3])
            symbol = cmd_parts[4].upper()
            if tf and symbol in self.symbols and ma_type in ['fast', 'slow', 'exit_fast', 'exit_slow']:
                self.ma_configs[tf][ma_type] = period
                return f"{ma_type.capitalize()} MA set to {period} for {symbol} on {self.get_timeframe_name(tf)}."
            return "Usage: /config_ma <timeframe> <fast/slow/exit_fast/exit_slow> <period> <symbol>"

        if cmd == "config_ma_bulk" and len(cmd_parts) >= 3:
            configs = " ".join(cmd_parts[1:]).split(';')
            updated = []
            for config in configs:
                parts = config.strip().split()
                if len(parts) != 4:
                    continue
                tf, ma_type, period, symbol = parts[0], parts[1].lower(), int(parts[2]), parts[3].upper()
                tf_val = self.parse_timeframe(tf)
                if tf_val and symbol in self.symbols and ma_type in ['fast', 'slow', 'exit_fast', 'exit_slow']:
                    self.ma_configs[tf_val][ma_type] = period
                    updated.append(f"{ma_type}={period} on {tf} for {symbol}")
            return f"Bulk MA config updated: {', '.join(updated)}" if updated else "No valid configs provided."

        if cmd == "setparams":
            return self.handle_position_params(cmd_parts)

        if cmd == "gen_report":
            try:
                if len(cmd_parts) < 2:
                    return "Usage: gen_report --ticket <ticket> | --symbol <symbol> | --daily"
                
                if cmd_parts[1] == "--ticket" and len(cmd_parts) >= 3:
                    return self.generate_trade_report(ticket=int(cmd_parts[2]))
                elif cmd_parts[1] == "--symbol" and len(cmd_parts) >= 3:
                    return self.generate_trade_report(symbol=cmd_parts[2].upper())
                elif cmd_parts[1] == "--daily":
                    return self.generate_trade_report(daily=True)
                else:
                    return "Invalid report type. Use --ticket, --symbol, or --daily"
            except Exception as e:
                return f"Error generating report: {str(e)}"
                
        if cmd == "status":
            status_lines = [f"Trading System Status for Scope {', '.join(scope)}:"]
            status_lines.append(f"Trading Allowed: {', '.join([f'{sym}: {self.trading_allowed[sym]}' for sym in scope])}")
            status_lines.append(f"Daily Profit: {', '.join([f'{sym}: {self.convert_to_points(self.daily_profit[sym], sym):.2f} points' for sym in scope])}")
            status_lines.append(f"Open Positions: {sum(len(self.positions[sym]) for sym in scope)}")
            status_lines.append("Strategy States:")
            status_lines.append(f"  Primary: {'Semi-Auto' if self.primary_strategy_semi_auto else 'Full Auto' if self.primary_strategy_enabled else 'Disabled'}")
            status_lines.append(f"  SureTrend: {'Semi-Auto' if self.suretrend_semi_auto else 'Full Auto' if self.suretrend_automation_enabled else 'Disabled'}")
            status_lines.append(f"  Grid: {'Semi-Auto' if self.grid_semi_auto else 'Full Auto' if self.grid_trading_enabled else 'Disabled'}")
            status_lines.append(f"  Momentum: {'Semi-Auto' if self.momentum_semi_auto else 'Full Auto' if self.momentum_automation_enabled else 'Disabled'}")
            status_lines.append(f"Dynamic Management: {self.dynamic_management_enabled}")
            status_lines.append(f"Exit Signals: {self.exit_signals_enabled}")
            status_lines.append(f"Lot Size: {self.lot_size:.2f}")
            status_lines.append(f"Daily Profit Limit: {self.daily_max_profit:.2f} points")
            status_lines.append(f"Simulation Mode: {self.simulate}")
            for symbol in scope:
                for tf in self.timeframes:
                    tf_name = self.get_timeframe_name(tf)
                    if self.suretrend_conditions_met[symbol][tf]['buy']:
                        status_lines.append(f"SureTrend BUY conditions met for {symbol} on {tf_name}")
                    elif self.suretrend_conditions_met[symbol][tf]['sell']:
                        status_lines.append(f"SureTrend SELL conditions met for {symbol} on {tf_name}")
            return "\n".join(status_lines)

        if cmd == "gen_report":
            try:
                if len(cmd_parts) < 2:
                    return "Usage: gen_report [--ticket TICKET | --symbol SYMBOL | --daily]"
                
                if "--ticket" in cmd_parts:
                    ticket_idx = cmd_parts.index("--ticket") + 1
                    if ticket_idx >= len(cmd_parts):
                        return "Missing ticket number"
                    return self.generate_trade_report(ticket=int(cmd_parts[ticket_idx]))
                
                elif "--symbol" in cmd_parts:
                    symbol_idx = cmd_parts.index("--symbol") + 1
                    if symbol_idx >= len(cmd_parts):
                        return "Missing symbol"
                    return self.generate_trade_report(symbol=cmd_parts[symbol_idx].upper())
                
                elif "--daily" in cmd_parts:
                    return self.generate_trade_report(daily=True)
                
                return "Invalid report parameters"
                
            except Exception as e:
                self.logger.error(f"Error handling gen_report command: {str(e)}")
                return f"Error generating report: {str(e)}"

        if cmd == "help":
            help_lines = [
                "🤖 Trading Bot Command Guide",
                "",
                "📈 Strategy Management:",
                "  enable_primary_strategy/disable_primary_strategy - Control primary strategy",
                "  enable_suretrend_automation/disable_suretrend_automation - Control SureTrend",
                "  enable_grid_trading/disable_grid_trading - Control grid trading",
                "  enable_momentum_automation/disable_momentum_automation - Control momentum",
                "  enable_hfscalper/disable_hfscalper - Control HFScalper strategy",
                "",
                "🔄 Semi-Auto Mode:",
                "  enable_primary_semi_auto/disable_primary_semi_auto - Control primary semi-auto",
                "  enable_suretrend_semi_auto/disable_suretrend_semi_auto - Control SureTrend semi-auto",
                "  enable_grid_semi_auto/disable_grid_semi_auto - Control grid semi-auto",
                "  enable_momentum_semi_auto/disable_momentum_semi_auto - Control momentum semi-auto",
                "  enable_hfscalper_semi_auto/disable_hfscalper_semi_auto - Control HFScalper semi-auto",
                "",
                "⚙️ Strategy Configuration:",
                "  set_hfscalper_min_momentum <value> - Set minimum momentum threshold",
                "  set_hfscalper_volatility <value> - Set volatility threshold",
                "  set_hfscalper_tp <points> - Set take profit in points",
                "  set_hfscalper_psar_step <value> - Set PSAR step",
                "  set_hfscalper_psar_max <value> - Set PSAR maximum",
                "  enable_hfscalper_psar/disable_hfscalper_psar - Control HFScalper PSAR filter",
                "",
                "👥 Account Management:",
                "  add_account <name> <login> <password> <server> - Add trading account",
                "  switch_account <name> - Switch to specified account",
                "  enable_sync/disable_sync - Control multi-account synchronization",
                "  list_accounts - Show configured accounts",
                "",
                "💹 Basic Trading Commands:",
                "  buy_market <timeframe> <symbol> - Place market buy order",
                "  sell_market <timeframe> <symbol> - Place market sell order",
                "  m1b/m5b/.../h4b <symbol> - Buy with strategy checks",
                "  m1s/m5s/.../h4s <symbol> - Sell with strategy checks",
                "  m1b0/m5b0/.../h4b0 <symbol> - Immediate buy without checks",
                "  m1s0/m5s0/.../h4s0 <symbol> - Immediate sell without checks",
                "",
                "📊 TP-Based Trading:",
                "  <points>b/s <symbol> [timeframe] - Trade with TP on MA crossover",
                "  <points>b0/s0 <symbol> [timeframe] - Immediate trade with TP",
                "  Valid points: 50, 100, 150, 200, 250, 300, 350, 400, 500, 600, 800, 1000, 2000",
                "",
                "🎯 Position Management:",
                "  close <ticket> - Close specific position",
                "  close_all - Close all open positions",
                "  close_partial <symbol> <ticket> <percent> - Close part of position",
                "  add_to_position <symbol> <ticket> <lots> - Add to position",
                "  set_sl <symbol> <ticket> <value> - Set stop loss",
                "  set_tp <symbol> <ticket> <value> - Set take profit",
                "  modify <symbol> <ticket> <sl/tp> <value> - Modify SL/TP",
                "  setparams <ticket> <sl_points> <tp_points> <trail_stop> <trail_delay> <ma_exit> - Set position parameters",
                "",
                "📈 Signal Optimization:",
                "  optimize_signals - Enable signal optimization",
                "  disable_signal_optimization - Disable signal optimization",
                "  set_signal_interval <seconds> - Set signal check interval",
                "  get_signal_stats [symbol] [timeframe] - Get signal performance",
                "  enable_realtime_signals/disable_realtime_signals - Control real-time signals",
                "  set_signal_threshold <value> - Set signal quality threshold",
                "  enable_signal_alerts/disable_signal_alerts - Control signal alerts",
                "  enable_signal_logging/disable_signal_logging - Control signal logging",
                "",
                "⚙️ Risk Management:",
                "  set_lot_size <value> - Set default lot size",
                "  set_daily_profit_limit <value> - Set daily profit limit",
                "  set_breakeven <timeframe> <points> - Set breakeven trigger",
                "  set_trailing_stop <timeframe> <points> - Set trailing stop",
                "  set_trailing_delay <timeframe> <points> - Set trailing activation",
                "  set_cooldown <seconds> - Set signal cooldown",
                "",
                "🔍 Analysis & Filters:",
                "  enable_volatility/disable_volatility <timeframe> <symbol> - Control volatility check",
                "  enable_psar_filter/disable_psar_filter <timeframe> <symbol> - Control PSAR filter",
                "  enable_dynamic_management/disable_dynamic_management - Control dynamic management",
                "  enable_exit_signals/disable_exit_signals - Control exit signals",
                "  m1_exit/m5_exit/.../h4_exit <on/off> <symbol> - Control MA exits",
                "",
                "📊 Moving Average Configuration:",
                "  config_ma <timeframe> <type> <period> <symbol> - Configure single MA",
                "  config_ma_bulk <configs> - Bulk configure MAs",
                "  Types: fast, slow, exit_fast, exit_slow",
                "",
                "📈 Monitoring & Reports:",
                "  status - Show system status",
                "  metrics - Show detailed metrics",
                "  history - Show recent trade history",
                "  daily_history <symbol> - Show today's trades",
                "  fetch_suretrend_history <symbol> - Show SureTrend trades",
                "  strategy_history <strategy> <symbol> - Show strategy-specific trades",
                "  fetch_chart <symbol> <timeframe> - Generate chart",
                "  gen_report --ticket <ticket> - Generate ticket report",
                "  gen_report --symbol <symbol> - Generate symbol report",
                "  gen_report --daily - Generate daily report",
                "",
                "💬 Trade Information:",
                "  comment <ticket> <text> - Add comment to position",
                "  reason <ticket> <text> - Update trade reason",
                "",
                "🔒 Trading Lock Commands:",
                "  unlock_trading <password> - Unlock trading (admin only)",
                "  trading_status - Check current trading lock status",
                "",
                "⚡ Quick Commands:",
                "  cd <symbol> | .. - Set/reset context symbol",
                "  stop - Stop trading",
                "  start - Start trading",
                "  resume <symbol> - Resume symbol trading",
                "  yes - Confirm pending semi-auto trade",
                "  no - Reject pending semi-auto trade",
                "  exit - Exit the program"
            ]
            return "\n".join(help_lines)

        if cmd == "fetch_chart" and len(cmd_parts) >= 3:
            try:
                symbol = cmd_parts[1].upper()
                timeframe = cmd_parts[2].upper()
                
                if symbol not in self.symbols:
                    return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"
                
                if timeframe not in self.timeframe_configs:
                    return f"Invalid timeframe: {timeframe}. Available timeframes: {', '.join(self.timeframe_configs.keys())}"
                
                result = self.fetch_chart(symbol, timeframe)
                return result
            except Exception as e:
                self.logger.error(f"Error in fetch_chart command: {str(e)}")
                return f"Error generating chart: {str(e)}"

        if cmd == "manual_tp" and len(cmd_parts) >= 5:
            symbol = cmd_parts[1].upper()
            timeframe = self.parse_timeframe(cmd_parts[2])
            direction = cmd_parts[3].upper()
            tp_points = int(cmd_parts[4])
            return self.execute_manual_tp_trade(symbol, timeframe, direction, tp_points)

        if cmd == "strategy_history" and len(cmd_parts) >= 3:
            strategy = cmd_parts[1].lower()
            symbol = cmd_parts[2].upper()
            return self.fetch_strategy_history(strategy, symbol)

        if cmd == "momentum" and len(cmd_parts) >= 3:
            symbol = cmd_parts[1].upper()
            timeframe = self.parse_timeframe(cmd_parts[2])
            return self.execute_momentum_strategy(symbol, timeframe)

        if cmd == "enable_primary_semi_auto":
            self.primary_strategy_semi_auto = True
            return f"Primary strategy semi-automated mode enabled for scope {', '.join(scope)}."

        if cmd == "disable_primary_semi_auto":
            self.primary_strategy_semi_auto = False
            return f"Primary strategy semi-automated mode disabled for scope {', '.join(scope)}."

        if cmd == "enable_suretrend_semi_auto":
            self.suretrend_semi_auto = True
            return f"SureTrend semi-automated mode enabled for scope {', '.join(scope)}."

        if cmd == "disable_suretrend_semi_auto":
            self.suretrend_semi_auto = False
            return f"SureTrend semi-automated mode disabled for scope {', '.join(scope)}."

        if cmd == "enable_grid_semi_auto":
            self.grid_semi_auto = True
            return f"Grid trading semi-automated mode enabled for scope {', '.join(scope)}."

        if cmd == "disable_grid_semi_auto":
            self.grid_semi_auto = False
            return f"Grid trading semi-automated mode disabled for scope {', '.join(scope)}."

        if cmd == "enable_momentum_semi_auto":
            self.momentum_semi_auto = True
            return f"Momentum strategy semi-automated mode enabled for scope {', '.join(scope)}."

        if cmd == "disable_momentum_semi_auto":
            self.momentum_semi_auto = False
            return f"Momentum strategy semi-automated mode disabled for scope {', '.join(scope)}."

        if cmd == "fetch_chart":
            try:
                if len(cmd_parts) < 3:
                    return "Usage: fetch_chart <symbol> <timeframe>"
                
                symbol = cmd_parts[1].upper()
                timeframe = cmd_parts[2].upper()
                
                if symbol not in self.symbols:
                    return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"
                
                if timeframe not in self.timeframe_configs:
                    return f"Invalid timeframe: {timeframe}. Available timeframes: {', '.join(self.timeframe_configs.keys())}"
                
                return self.fetch_chart(symbol, timeframe)
            except Exception as e:
                self.logger.error(f"Error in fetch_chart command: {str(e)}")
                return f"Error generating chart: {str(e)}"

        if cmd == "enable_hfscalper":
            self.hfscalper_enabled = True
            return f"HFScalper strategy enabled for scope {', '.join(scope)}."

        if cmd == "disable_hfscalper":
            self.hfscalper_enabled = False
            return f"HFScalper strategy disabled for scope {', '.join(scope)}."

        if cmd == "enable_hfscalper_semi_auto":
            self.hfscalper_semi_auto = True
            return f"HFScalper semi-automated mode enabled for scope {', '.join(scope)}."

        if cmd == "disable_hfscalper_semi_auto":
            self.hfscalper_semi_auto = False
            return f"HFScalper semi-automated mode disabled for scope {', '.join(scope)}."

        if cmd == "enable_hfscalper_psar":
            self.hfscalper_psar_enabled = True
            return f"HFScalper PSAR filter enabled for scope {', '.join(scope)}."

        if cmd == "disable_hfscalper_psar":
            self.hfscalper_psar_enabled = False
            return f"HFScalper PSAR filter disabled for scope {', '.join(scope)}."

        if cmd == "set_hfscalper_min_momentum" and len(cmd_parts) >= 2:
            try:
                value = float(cmd_parts[1])
                if value <= 0:
                    return "Minimum momentum must be positive."
                self.hfscalper_min_momentum = value
                return f"HFScalper minimum momentum set to {value}."
            except ValueError:
                return f"Invalid value '{cmd_parts[1]}'. Please provide a numeric value."

        if cmd == "set_hfscalper_volatility" and len(cmd_parts) >= 2:
            try:
                value = float(cmd_parts[1])
                if value <= 0:
                    return "Volatility threshold must be positive."
                self.hfscalper_volatility_threshold = value
                return f"HFScalper volatility threshold set to {value}."
            except ValueError:
                return f"Invalid value '{cmd_parts[1]}'. Please provide a numeric value."

        if cmd == "set_hfscalper_tp" and len(cmd_parts) >= 2:
            try:
                points = int(cmd_parts[1])
                if points <= 0:
                    return "Take profit points must be positive."
                self.hfscalper_tp_points = points
                return f"HFScalper take profit set to {points} points."
            except ValueError:
                return f"Invalid value '{cmd_parts[1]}'. Please provide a numeric value."

        if cmd == "set_hfscalper_psar_step" and len(cmd_parts) >= 2:
            try:
                value = float(cmd_parts[1])
                if value <= 0:
                    return "PSAR step must be positive."
                self.hfscalper_psar_step = value
                return f"HFScalper PSAR step set to {value}."
            except ValueError:
                return f"Invalid value '{cmd_parts[1]}'. Please provide a numeric value."

        if cmd == "set_hfscalper_psar_max" and len(cmd_parts) >= 2:
            try:
                value = float(cmd_parts[1])
                if value <= 0:
                    return "PSAR maximum must be positive."
                self.hfscalper_psar_max = value
                return f"HFScalper PSAR maximum set to {value}."
            except ValueError:
                return f"Invalid value '{cmd_parts[1]}'. Please provide a numeric value."

        return f"Unknown command: {command}. Type 'help' for available commands."

    def parse_command(self, command):
        """Parse trading commands into their components."""
        cmd_parts = command.lower().split()
        if not cmd_parts:
            return None, None, None, None

        cmd = cmd_parts[0]
        
        # Handle immediate TP commands (e.g., "100b0", "500s0")
        tp_immediate_match = re.match(r'(\d+)(b0|s0)$', cmd)
        if tp_immediate_match:
            tp_points = int(tp_immediate_match.group(1))
            direction = "BUY" if tp_immediate_match.group(2) == 'b0' else "SELL"
            symbol = cmd_parts[1].upper() if len(cmd_parts) > 1 else None
            timeframe = self.parse_timeframe(cmd_parts[2]) if len(cmd_parts) > 2 else mt5.TIMEFRAME_M1
            return "tp_immediate_trade", {"points": tp_points, "direction": direction, "symbol": symbol, "timeframe": timeframe}
        
        # Handle numeric TP commands (e.g., "100b", "500s")
        tp_match = re.match(r'(\d+)(b|s)$', cmd)
        if tp_match:
            tp_points = int(tp_match.group(1))
            direction = "BUY" if tp_match.group(2) == 'b' else "SELL"
            symbol = cmd_parts[1].upper() if len(cmd_parts) > 1 else None
            timeframe = self.parse_timeframe(cmd_parts[2]) if len(cmd_parts) > 2 else mt5.TIMEFRAME_M1
            return "tp_trade", {"points": tp_points, "direction": direction, "symbol": symbol, "timeframe": timeframe}
        
        # Handle timeframe-based commands (e.g., "m1b", "h4s")
        tf_match = re.match(r'(m1|m5|m15|m30|h1|h4)(b|s|b0|s0)$', cmd)
        if tf_match:
            tf_str = tf_match.group(1).upper()
            action = tf_match.group(2)
            timeframe = self.timeframe_configs.get(tf_str)
            direction = "BUY" if action.startswith('b') else "SELL"
            immediate = action.endswith('0')
            symbol = cmd_parts[1].upper() if len(cmd_parts) > 1 else None
            return "timeframe_trade", {"timeframe": timeframe, "direction": direction, "immediate": immediate, "symbol": symbol}
        
        return "standard", cmd_parts

    def handle_terminal_command(self, command):
        # First ensure we're synced with MT5
        self.sync_with_mt5()
        
        cmd_parts = command.strip().split()
        if not cmd_parts:
            return "No command provided."
            
        cmd = cmd_parts[0].lower()
        
        # Add new SureTrend monitoring commands
        if cmd == "start_suretrend_monitor":
            self.start_suretrend_monitoring()
            return "SureTrend condition monitoring started."
            
        if cmd == "stop_suretrend_monitor":
            self.stop_suretrend_monitoring()
            return "SureTrend condition monitoring stopped."
            
        if cmd == "show_suretrend":
            if len(cmd_parts) > 1:
                symbol = cmd_parts[1].upper()
                timeframe = None
                if len(cmd_parts) > 2:
                    timeframe = self.parse_timeframe(cmd_parts[2])
                return self.display_suretrend_checklist(symbol, timeframe)
            else:
                return self.display_suretrend_checklist()
        
        if cmd == "mock_trade" and len(cmd_parts) >= 3:
            symbol = cmd_parts[1].upper()
            trade_type = cmd_parts[2].upper()
            lot_size = float(cmd_parts[3]) if len(cmd_parts) > 3 else 0.01

            if trade_type not in ["BUY", "SELL"]:
                return "Invalid trade type. Use BUY or SELL"

            return self.mock_trade(symbol, trade_type, lot_size)
            self.sync_positions_with_mt5()

        cmd_parts = command.lower().split()
        if not cmd_parts:
            return "🤔 Empty command received. Type 'help' for available commands."

        cmd = cmd_parts[0]

        if cmd == "unlock_trading" and len(cmd_parts) >= 2:
            password = cmd_parts[1]
            return self.unlock_trading(password)

        if cmd == "trading_status":
            if self.trading_locked:
                return f"🔒 Trading is currently locked\nReason: {self.trading_lock_reason}"
            return "✅ Trading is active"

        if cmd == "gen_report":
            try:
                if len(cmd_parts) < 2:
                    return "Usage: gen_report --ticket <ticket> | --symbol <symbol> | --daily"
                
                if cmd_parts[1] == "--ticket" and len(cmd_parts) >= 3:
                    return self.generate_trade_report(ticket=int(cmd_parts[2]))
                elif cmd_parts[1] == "--symbol" and len(cmd_parts) >= 3:
                    return self.generate_trade_report(symbol=cmd_parts[2].upper())
                elif cmd_parts[1] == "--daily":
                    return self.generate_trade_report(daily=True)
                else:
                    return "Invalid report type. Use --ticket, --symbol, or --daily"
            except Exception as e:
                return f"Error generating report: {str(e)}"
        scope = self.context_symbol or self.symbols
        if isinstance(scope, str):
            scope = [scope]

        # Add new pattern for immediate TP-based trades
        tp_immediate_match = re.match(r'(\d+)(b0|s0)$', cmd)
        if tp_immediate_match and len(cmd_parts) >= 2:
            tp_points = int(tp_immediate_match.group(1))
            direction = "BUY" if tp_immediate_match.group(2) == 'b0' else "SELL"
            symbol = cmd_parts[1].upper()
            timeframe = self.parse_timeframe(cmd_parts[2]) if len(cmd_parts) > 2 else mt5.TIMEFRAME_M1
            
            if symbol in self.symbols and timeframe:
                tick = mt5.symbol_info_tick(symbol)
                if not tick:
                    return f"Failed to fetch tick data for {symbol}."
                
                price = tick.ask if direction == "BUY" else tick.bid
                order_type = mt5.ORDER_TYPE_BUY if direction == "BUY" else mt5.ORDER_TYPE_SELL
                
                # Calculate TP based on points
                tp = price + (tp_points * self.point[symbol]) if direction == "BUY" else price - (tp_points * self.point[symbol])
                sl = price - (self.initial_sl * self.point[symbol]) if direction == "BUY" else price + (self.initial_sl * self.point[symbol])
                
                success, position = self.open_position(
                    order_type, price, datetime.now(),
                    f"Immediate {tp_points} points TP Trade on {symbol}\nDirection: {direction}",
                    timeframe, symbol
                )
                
                if success:
                    # Update TP for the position
                    self.modify_position(position, tp=tp)
                    return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {sl:.5f}\n✨ TP: {tp:.5f}"
                return f"Failed to open {direction} position on {symbol} with TP {tp_points} points."
            return f"Invalid symbol '{symbol}' or timeframe '{cmd_parts[2] if len(cmd_parts) > 2 else 'M1'}'. Available symbols: {', '.join(self.symbols)}"

        if cmd == "metrics":
            try:
                # Force sync with MT5 before calculating metrics
                if not self.simulate:
                    self.sync_positions_with_mt5()
                
                metrics_lines = [f"📊 Detailed Trading Metrics Report for Scope {', '.join(scope)}:"]
                
                # Get current account info
                account_info = mt5.account_info() if not self.simulate else None
                balance = account_info.balance if account_info else self.initial_balance
                equity = account_info.equity if account_info else balance
                
                metrics_lines.append(f"💰 Account Balance: ${balance:.2f}")
                metrics_lines.append(f"📈 Equity: ${equity:.2f}")
                
                total_positions = sum(len(self.positions[sym]) for sym in scope)
                metrics_lines.append(f"📌 Total Open Positions: {total_positions}")
                
                # Calculate total daily profit
                total_points = 0
                for sym in scope:
                    if not self.simulate:
                        # Get current market prices for accurate profit calculation
                        tick = mt5.symbol_info_tick(sym)
                        if tick:
                            # Update profits for all positions
                            for pos in self.positions[sym].values():
                                if pos['type'] == mt5.ORDER_TYPE_BUY:
                                    pos['profit'] = (tick.bid - pos['entry_price']) * pos['lot_size'] * 10000
                                else:
                                    pos['profit'] = (pos['entry_price'] - tick.ask) * pos['lot_size'] * 10000
                
                    total_points += self.convert_to_points(self.daily_profit[sym], sym)
                
                metrics_lines.append(f"💵 Total Daily Profit: {total_points:.2f} points")
                metrics_lines.append("")
                
                for symbol in scope:
                    metrics_lines.append(f"🔍 {symbol} Metrics:")
                    open_positions = len(self.positions[symbol])
                    metrics_lines.append(f"  📊 Open Positions: {open_positions}")
                    
                    if open_positions > 0:
                        # Get current market prices
                        tick = mt5.symbol_info_tick(symbol) if not self.simulate else None
                        
                        for pos in self.positions[symbol].values():
                            # Verify position still exists in MT5
                            mt5_position = None if self.simulate else mt5.positions_get(ticket=pos['ticket'])
                            
                            if self.simulate or mt5_position:
                                current_profit = pos['profit']
                                if not self.simulate and tick:
                                    # Calculate real-time profit
                                    if pos['type'] == mt5.ORDER_TYPE_BUY:
                                        current_profit = (tick.bid - pos['entry_price']) * pos['lot_size'] * 10000
                                    else:
                                        current_profit = (pos['entry_price'] - tick.ask) * pos['lot_size'] * 10000
                                
                                profit_points = self.convert_to_points(current_profit, symbol)
                                
                                metrics_lines.append(
                                    f"    🎫 Ticket {pos['ticket']}: {pos['lot_size']} lots\n"
                                    f"       💰 Entry: {pos['entry_price']:.5f}\n"
                                    f"       🛑 SL: {pos['sl']:.5f}\n"
                                    f"       ✨ TP: {pos['tp']:.5f}\n"
                                    f"       📈 Current Profit: {profit_points:.2f} points\n"
                                    f"       📋 Strategy: {pos['strategy']}"
                                )
                    
                    daily_profit_points = self.convert_to_points(self.daily_profit[symbol], symbol)
                    metrics_lines.append(f"  💵 Daily Profit: {daily_profit_points:.2f} points")
                    metrics_lines.append(f"  📊 Total Trades Today: {len(self.daily_trades[symbol])}")
                
                return "\n".join(metrics_lines) if total_positions > 0 else f"No open positions in scope {', '.join(scope)}."
                
            except Exception as e:
                self.logger.error(f"Error generating metrics: {str(e)}")
                return f"Error generating metrics: {str(e)}"

        if cmd == "cd":
            if len(cmd_parts) >= 2:
                if cmd_parts[1] == "..":
                    self.context_symbol = None
                    return "📍 Context set to all symbols. All commands will now apply to all symbols."
                symbol = cmd_parts[1].upper()
                if symbol in self.symbols:
                    self.context_symbol = symbol
                    return f"📍 Context set to {symbol}. All commands will now apply to {symbol} only."
                return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"
            return "Usage: cd <symbol> | .."

        if cmd == "add_account" and len(cmd_parts) == 5:
            name, login, password, server = cmd_parts[1], cmd_parts[2], cmd_parts[3], cmd_parts[4]
            if self.add_account(name, login, password, server):
                return f"✅ Account '{name}' added successfully!\n🏦 Server: {server}\n🔑 Login: {login}"
            return f"Failed to add account '{name}'."
    
        if cmd == "switch_account" and len(cmd_parts) == 2:
            name = cmd_parts[1]
            if self.switch_account(name):
                return f"Switched to account '{name}'."
            return f"Failed to switch to account '{name}'."
    
        if cmd == "enable_sync":
            self.sync_enabled = True
            return "Account synchronization enabled."
    
        if cmd == "disable_sync":
            self.sync_enabled = False
            return "Account synchronization disabled."
    
        if cmd == "list_accounts":
            if not self.accounts:
                return "No trading accounts configured"
            account_info = []
            for name, details in self.accounts.items():
                status = "Active" if name == self.current_account else "Inactive"
                account_info.append(f"{name}: {details['server']} ({status})")
            return "Trading Accounts:\n" + "\n".join(account_info)

        if cmd == "stop":
            for symbol in scope:
                self.trading_allowed[symbol] = False
            return f"Trading stopped for {', '.join(scope)}."

        if cmd == "start":
            for symbol in scope:
                self.trading_allowed[symbol] = True
            return f"Trading started for {', '.join(scope)}."

        if cmd == "resume" and len(cmd_parts) >= 2:
            symbol = cmd_parts[1].upper()
            if symbol in self.symbols:
                self.trading_allowed[symbol] = True
                return f"Trading resumed for {symbol}."
            return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"

        def close_position_task(position):
            nonlocal closed, failed
            try:
                success = self.close_position(position, "Manual close_all")
                if success:
                    closed += 1
                else:
                    failed += 1
            except Exception as e:
                self.logger.error(f"Error closing position {position['ticket']}: {str(e)}")
                failed += 1

        if cmd == "close_all":
            closed = 0
            failed = 0
            try:
                # Acquire lock once for the entire operation
                if not self.command_lock.acquire(timeout=10):  # Increased timeout
                    return "Failed to acquire lock for close_all operation"
                
                try:
                    positions_to_close = []
                    for symbol in scope:
                        positions_to_close.extend(list(self.positions[symbol].values()))
                    
                    if not positions_to_close:
                        self.command_lock.release()
                        return "No open positions to close"
                    
                    # Close positions sequentially to avoid MT5 issues
                    for position in positions_to_close:
                        try:
                            success = self.close_position(position, "Manual close_all")
                            if success:
                                closed += 1
                            else:
                                failed += 1
                        except Exception as e:
                            self.logger.error(f"Error closing position {position['ticket']}: {str(e)}")
                            failed += 1
                        
                        # Small delay between closes to avoid overwhelming MT5
                        time.sleep(0.1)
                    
                finally:
                    if self.command_lock.locked():
                        self.command_lock.release()

                if closed > 0:
                    return f"✅ Successfully closed {closed} positions" + (f", {failed} failed" if failed > 0 else "")
                elif failed > 0:
                    return f"❌ Failed to close {failed} positions"
                return "No open positions to close"
                
            except Exception as e:
                self.logger.error(f"Error in close_all command: {str(e)}")
                if self.command_lock.locked():
                    self.command_lock.release()
                return f"Error executing close_all command: {str(e)}"

        if cmd == "close" and len(cmd_parts) >= 2:
            ticket = int(cmd_parts[1])
            for symbol in scope:
                if ticket in self.positions[symbol]:
                    success = self.close_position(self.positions[symbol][ticket], "Manual close")
                    return f"Position {ticket} closed successfully for {symbol}." if success else f"Failed to close position {ticket} for {symbol}."
            return f"Position with ticket {ticket} not found in scope {', '.join(scope)}."

        if cmd == "close_partial" and len(cmd_parts) >= 4:
            symbol = cmd_parts[1].upper()
            ticket = int(cmd_parts[2])
            pct = float(cmd_parts[3])
            if symbol in self.symbols and ticket in self.positions[symbol]:
                position = self.positions[symbol][ticket]
                partial_lot = position['lot_size'] * (pct / 100)
                if self.simulate:
                    current_price = random.uniform(position['entry_price'] - 50 * self.point[symbol], position['entry_price'] + 50 * self.point[symbol])
                    profit_points = self.convert_to_points(
                        (current_price - position['entry_price']) * partial_lot * 10000 if position['type'] == mt5.ORDER_TYPE_BUY else
                        (position['entry_price'] - current_price) * partial_lot * 10000, symbol)
                    position['lot_size'] -= partial_lot
                    if position['lot_size'] <= 0:
                        del self.positions[symbol][ticket]
                        return f"Partially closed ticket {ticket} for {symbol}: {pct}% ({partial_lot:.2f} lots), Simulated Profit: {profit_points:.2f} points. Position fully closed."
                    self.daily_profit[symbol] += profit_points * self.point[symbol] * partial_lot * 10000
                    return f"Partially closed ticket {ticket} for {symbol}: {pct}% ({partial_lot:.2f} lots), Simulated Profit: {profit_points:.2f} points. Remaining lots: {position['lot_size']:.2f}."
                else:
                    request = {
                        "action": mt5.TRADE_ACTION_DEAL,
                        "symbol": symbol,
                        "volume": partial_lot,
                        "type": mt5.ORDER_TYPE_SELL if position['type'] == mt5.ORDER_TYPE_BUY else mt5.ORDER_TYPE_BUY,
                        "position": ticket,
                        "price": mt5.symbol_info_tick(symbol).bid if position['type'] == mt5.ORDER_TYPE_BUY else mt5.symbol_info_tick(symbol).ask,
                        "deviation": self.deviation,
                        "magic": 234000,
                        "comment": "Partial close",
                        "type_time": mt5.ORDER_TIME_GTC,
                        "type_filling": mt5.ORDER_FILLING_IOC
                    }
                    result = mt5.order_send(request)
                    if result.retcode == mt5.TRADE_RETCODE_DONE:
                        position['lot_size'] -= partial_lot
                        profit_points = self.convert_to_points(result.profit, symbol) if hasattr(result, 'profit') else 0
                        self.daily_profit[symbol] += profit_points * self.point[symbol] * partial_lot * 10000
                        if position['lot_size'] <= 0:
                            del self.positions[symbol][ticket]
                            return f"Partially closed ticket {ticket} for {symbol}: {pct}% ({partial_lot:.2f} lots), Profit: {profit_points:.2f} points. Position fully closed."
                        return f"Partially closed ticket {ticket} for {symbol}: {pct}% ({partial_lot:.2f} lots), Profit: {profit_points:.2f} points. Remaining lots: {position['lot_size']:.2f}."
                    return f"Failed to partially close ticket {ticket} for {symbol}: {result.comment}"
            return f"Invalid symbol '{symbol}' or ticket {ticket} not found."

        if cmd == "add_to_position" and len(cmd_parts) >= 4:
            symbol = cmd_parts[1].upper()
            ticket = int(cmd_parts[2])
            lot = float(cmd_parts[3])
            if symbol in self.symbols and ticket in self.positions[symbol]:
                position = self.positions[symbol][ticket]
                if self.simulate:
                    position['lot_size'] += lot
                    return f"Simulated addition of {lot:.2f} lots to ticket {ticket} for {symbol}. New lot size: {position['lot_size']:.2f}."
                else:
                    request = {
                        "action": mt5.TRADE_ACTION_DEAL,
                        "symbol": symbol,
                        "volume": lot,
                        "type": position['type'],
                        "price": mt5.symbol_info_tick(symbol).ask if position['type'] == mt5.ORDER_TYPE_BUY else mt5.symbol_info_tick(symbol).bid,
                        "deviation": self.deviation,
                        "magic": 234000,
                        "comment": "Add to position",
                        "type_time": mt5.ORDER_TIME_GTC,
                        "type_filling": mt5.ORDER_FILLING_IOC
                    }
                    result = mt5.order_send(request)
                    if result.retcode == mt5.TRADE_RETCODE_DONE:
                        position['lot_size'] += lot
                        return f"Added {lot:.2f} lots to ticket {ticket} for {symbol}. New lot size: {position['lot_size']:.2f}."
                    return f"Failed to add {lot:.2f} lots to ticket {ticket} for {symbol}: {result.comment}"
            return f"Invalid symbol '{symbol}' or ticket {ticket} not found."

        if cmd == "buy_market" and len(cmd_parts) >= 3:
            timeframe = self.parse_timeframe(cmd_parts[1])
            symbol = cmd_parts[2].upper()
            if timeframe and symbol in self.symbols:
                tick = mt5.symbol_info_tick(symbol)
                if not tick:
                    return f"Failed to fetch tick data for {symbol}."
                price = tick.ask
                success, position = self.open_position(mt5.ORDER_TYPE_BUY, price, datetime.now(),
                                                      f"Manual BUY via Terminal on {self.get_timeframe_name(timeframe)} at {price:.2f}",
                                                      timeframe, symbol)
                return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {position['sl']:.5f}\n✨ TP: {position['tp']:.5f}" if success else \
                       f"Failed to place market buy order for {symbol}."
            return f"Invalid timeframe '{cmd_parts[1]}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "sell_market" and len(cmd_parts) >= 3:
            timeframe = self.parse_timeframe(cmd_parts[1])
            symbol = cmd_parts[2].upper()
            if timeframe and symbol in self.symbols:
                tick = mt5.symbol_info_tick(symbol)
                if not tick:
                    return f"Failed to fetch tick data for {symbol}."
                price = tick.bid
                success, position = self.open_position(mt5.ORDER_TYPE_SELL, price, datetime.now(),
                                                      f"Manual SELL via Terminal on {self.get_timeframe_name(timeframe)} at {price:.2f}",
                                                      timeframe, symbol)
                return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {position['sl']:.5f}\n✨ TP: {position['tp']:.5f}" if success else \
                       f"Failed to place market sell order for {symbol}."
            return f"Invalid timeframe '{cmd_parts[1]}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd in ["m1b", "m5b", "m15b", "m30b", "h1b", "h4b", "m1s", "m5s", "m15s", "m30s", "h1s", "h4s"] and len(cmd_parts) >= 2:
            tf = cmd[:2].upper()
            direction = cmd[2].upper()
            symbol = cmd_parts[1].upper()
            if tf in self.timeframe_configs and symbol in self.symbols:
                timeframe = self.timeframe_configs[tf]
                conditions_met, message = self.check_manual_trade_conditions(symbol, timeframe, "BUY" if direction == "B" else "SELL")
                if not conditions_met:
                    return f"Cannot place {direction} trade on {symbol} {tf}: {message}"
                order_type = mt5.ORDER_TYPE_BUY if direction == "B" else mt5.ORDER_TYPE_SELL
                tick = mt5.symbol_info_tick(symbol)
                if not tick:
                    return f"Failed to fetch tick data for {symbol}."
                price = tick.ask if direction == "B" else tick.bid
                success, position = self.open_position(order_type, price, datetime.now(),
                                                      f"{tf} {direction} Manual Trade on {symbol}\nConditions: {message}",
                                                      timeframe, symbol)
                return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {position['sl']:.5f}\n✨ TP: {position['tp']:.5f}" if success else \
                       f"Failed to open {direction} position on {symbol} {tf}."
            return f"Invalid timeframe '{tf}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd in ["50b", "100b", "150b", "200b", "250b", "300b", "350b", "400b", "500b", "600b", "800b", "1000b", "2000b",
                   "50s", "100s", "150s", "200s", "250s", "300s", "350s", "400s", "500s", "600s", "800s", "1000s", "2000s"] and len(cmd_parts) >= 3:
            tp_points = int(cmd[:-1])
            direction = cmd[-1].upper()
            symbol = cmd_parts[1].upper()
            timeframe = self.parse_timeframe(cmd_parts[2]) if len(cmd_parts) > 2 else mt5.TIMEFRAME_M1
            if symbol in self.symbols and timeframe:
                conditions_met, message = self.check_manual_trade_conditions(symbol, timeframe, "BUY" if direction == "B" else "SELL")
                if not conditions_met:
                    return f"Cannot place {direction} trade with TP {tp_points} on {symbol}: {message}"
                tick = mt5.symbol_info_tick(symbol)
                if not tick:
                    return f"Failed to fetch tick data for {symbol}."
                price = tick.ask if direction == "B" else tick.bid
                order_type = mt5.ORDER_TYPE_BUY if direction == "B" else mt5.ORDER_TYPE_SELL
                sl = price - (self.initial_sl * self.point[symbol]) if order_type == mt5.ORDER_TYPE_BUY else price + (self.initial_sl * self.point[symbol])
                success, position = self.open_position(order_type, price, datetime.now(),
                                                      f"{tp_points}{direction} MA TP Trade on {symbol}\nConditions: {message}",
                                                      timeframe, symbol)
                if success:
                    self.positions[symbol][position['ticket']]['ma_tp_timeframe'] = timeframe
                    return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {sl:.2f}\n✨ TP: {position['tp']:.2f}"
                return f"Failed to open {direction} position on {symbol} with TP {tp_points} points."
            return f"Invalid symbol '{symbol}' or timeframe '{cmd_parts[2] if len(cmd_parts) > 2 else 'M1'}'. Available symbols: {', '.join(self.symbols)}"

        if cmd in ["m1b0", "m5b0", "m15b0", "m30b0", "h1b0", "h4b0", "m1s0", "m5s0", "m15s0", "m30s0", "h1s0", "h4s0"] and len(cmd_parts) >= 2:
            tf = cmd[:2].upper()
            direction = cmd[2].upper()
            symbol = cmd_parts[1].upper()
            if tf in self.timeframe_configs and symbol in self.symbols:
                timeframe = self.timeframe_configs[tf]
                order_type = mt5.ORDER_TYPE_BUY if direction == "B" else mt5.ORDER_TYPE_SELL
                tick = mt5.symbol_info_tick(symbol) if not self.simulate else None
                price = tick.ask if direction == "B" else tick.bid if tick else random.uniform(1000, 2000)
                success, position = self.open_position(order_type, price, datetime.now(),
                                                      f"{tf} {direction} Immediate Manual Trade on {symbol}",
                                                      timeframe, symbol)
                return f"🎯 Position opened: Ticket {position['ticket']}\n💰 Entry: {price:.5f}\n🛑 SL: {position['sl']:.5f}\n✨ TP: {position['tp']:.5f}" if success else \
                       f"Failed to open {direction} position on {symbol} {tf}."
            return f"Invalid timeframe '{tf}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "set_sl" and len(cmd_parts) >= 4:
            symbol = cmd_parts[1].upper()
            ticket = int(cmd_parts[2])
            value = float(cmd_parts[3])
            if symbol in self.symbols and ticket in self.positions[symbol]:
                self.modify_position(self.positions[symbol][ticket], sl=value)
                return f"Stop Loss set to {value:.2f} for ticket {ticket} on {symbol}."
            return f"Invalid symbol '{symbol}' or ticket {ticket} not found."

        if cmd == "set_tp" and len(cmd_parts) >= 4:
            symbol = cmd_parts[1].upper()
            ticket = int(cmd_parts[2])
            value = float(cmd_parts[3])
            if symbol in self.symbols and ticket in self.positions[symbol]:
                self.modify_position(self.positions[symbol][ticket], tp=value)
                return f"Take Profit set to {value:.2f} for ticket {ticket} on {symbol}."
            return f"Invalid symbol '{symbol}' or ticket {ticket} not found."

        if cmd == "modify" and len(cmd_parts) >= 5:
            symbol = cmd_parts[1].upper()
            ticket = int(cmd_parts[2])
            param = cmd_parts[3].lower()
            value = float(cmd_parts[4])
            if symbol in self.symbols and ticket in self.positions[symbol]:
                if param == "sl":
                    self.modify_position(self.positions[symbol][ticket], sl=value)
                    return f"Stop Loss modified to {value:.2f} for ticket {ticket} on {symbol}."
                elif param == "tp":
                    self.modify_position(self.positions[symbol][ticket], tp=value)
                    return f"Take Profit modified to {value:.2f} for ticket {ticket} on {symbol}."
                return f"Invalid parameter '{param}'. Use 'sl' or 'tp'."
            return f"Invalid symbol '{symbol}' or ticket {ticket} not found."

        if cmd == "comment" and len(cmd_parts) >= 3:
            ticket = int(cmd_parts[1])
            text = " ".join(cmd_parts[2:])
            for symbol in scope:
                if ticket in self.positions[symbol]:
                    self.positions[symbol][ticket]['comments'] = text
                    return f"Comment '{text}' added to ticket {ticket} for {symbol}."
            return f"Ticket {ticket} not found in scope {', '.join(scope)}."

        if cmd == "reason" and len(cmd_parts) >= 3:
            ticket = int(cmd_parts[1])
            text = " ".join(cmd_parts[2:])
            for symbol in scope:
                if ticket in self.positions[symbol]:
                    self.positions[symbol][ticket]['reason'] = text
                    return f"Reason updated to '{text}' for ticket {ticket} on {symbol}."
            return f"Ticket {ticket} not found in scope {', '.join(scope)}."

        if cmd == "history":
            history_lines = [f"Recent Trade History for Scope {', '.join(scope)}:"]
            
            for symbol in scope:
                history_lines.append(f"{symbol}:")
                
                try:
                    # Get current open positions from MT5
                    positions = mt5.positions_get(symbol=symbol) if not self.simulate else []
                    open_trades = []
                    if positions:
                        for pos in positions:
                            try:
                                current_profit = getattr(pos, 'profit', 0.0)
                                profit_points = self.convert_to_points(current_profit, symbol)
                                
                                trade = {
                                    "ticket": getattr(pos, 'ticket', 0),
                                    "type": "BUY" if getattr(pos, 'type', 0) == mt5.ORDER_TYPE_BUY else "SELL",
                                    "profit": current_profit,
                                    "profit_points": profit_points,
                                    "timeframe": self.get_timeframe_name(mt5.TIMEFRAME_M1),  # Default to M1 for open positions
                                    "entry_time": datetime.fromtimestamp(getattr(pos, 'time', datetime.now().timestamp())).strftime('%Y-%m-%d %H:%M:%S'),
                                    "symbol": getattr(pos, 'symbol', symbol),
                                    "status": "open",
                                    "lot_size": getattr(pos, 'volume', 0.01),
                                    "entry_price": getattr(pos, 'price_open', 0.0),
                                    "sl": getattr(pos, 'sl', 0.0),
                                    "tp": getattr(pos, 'tp', 0.0),
                                    "commission": 0.0,  # Default values for commission and swap
                                    "swap": getattr(pos, 'swap', 0.0),
                                    "comment": getattr(pos, 'comment', '') or "MT5 Trade"
                                }
                                open_trades.append(trade)
                            except Exception as e:
                                self.logger.debug(f"Error processing position {getattr(pos, 'ticket', 'unknown')}: {str(e)}")
                                continue
                
                    # Get closed trades from MT5 history
                    closed_trades = self.get_mt5_history(symbol)
                    
                    # Combine and sort all trades
                    all_trades = open_trades + closed_trades
                    all_trades.sort(key=lambda x: datetime.strptime(x['entry_time'], '%Y-%m-%d %H:%M:%S'), reverse=True)
                    
                    if not all_trades:
                        history_lines.append("  No trades found.")
                    else:
                        for trade in all_trades[:5]:  # Show last 5 trades
                            try:
                                status_info = f"[{trade.get('status', 'UNKNOWN').upper()}]"
                                profit_info = f"Profit: {trade.get('profit_points', 0.0):.2f} points (${trade.get('profit', 0.0):.2f})"
                                commission_info = f", Commission: ${trade.get('commission', 0.0):.2f}" if trade.get('commission', 0.0) != 0 else ""
                                swap_info = f", Swap: ${trade.get('swap', 0.0):.2f}" if trade.get('swap', 0.0) != 0 else ""
                                
                                entry_info = f"Entry: {trade.get('entry_time', 'Unknown')} @ {trade.get('entry_price', 0.0):.5f}"
                                close_info = f", Closed: {trade.get('close_time', '')} @ {trade.get('close_price', 0.0):.5f}" if trade.get('close_time') else ""
                                sl_tp_info = (f", SL: {trade.get('sl', 0.0):.5f}, TP: {trade.get('tp', 0.0):.5f}" 
                                            if trade.get('sl') is not None and trade.get('tp') is not None else "")
                                
                                comment_info = f", Comment: {trade.get('comment', '')}" if trade.get('comment') else ""
                                
                                history_lines.append(
                                    f"  {trade.get('type', 'UNKNOWN')} Ticket {trade.get('ticket', 'Unknown')}: {status_info}\n"
                                    f"    {profit_info}{commission_info}{swap_info}\n"
                                    f"    {entry_info}{close_info}{sl_tp_info}{comment_info}\n"
                                    f"    Volume: {trade.get('lot_size', 0.01):.2f} lots"
                                )
                            except Exception as e:
                                self.logger.debug(f"Error formatting trade {trade.get('ticket', 'unknown')}: {str(e)}")
                                continue
                    
                except Exception as e:
                    self.logger.error(f"Error processing trade history for {symbol}: {str(e)}")
                    history_lines.append(f"  Error processing trade history: {str(e)}")
                
            return "\n".join(history_lines)

        if cmd == "daily_history" and len(cmd_parts) >= 2:
            symbol = cmd_parts[1].upper()
            if symbol in self.symbols:
                today_start = datetime.now().replace(hour=0, minute=0, second=0, microsecond=0)
                history_lines = [f"Daily Trade History for {symbol} ({today_start.date()}):"]
                all_trades = self.trade_history[symbol] + self.grid_history[symbol] + self.suretrend_history[symbol] + self.momentum_history[symbol]
                trades = [trade for trade in all_trades 
                         if 'entry_time' in trade and datetime.strptime(trade['entry_time'], '%Y-%m-%d %H:%M:%S.%f') >= today_start]
                if not trades:
                    history_lines.append("  No trades executed today.")
                for trade in sorted(trades, key=lambda x: datetime.strptime(x['entry_time'], '%Y-%m-%d %H:%M:%S.%f')):
                    profit_points = self.convert_to_points(trade['profit'], symbol)
                    history_lines.append(f"  {trade['type']} Ticket {trade['ticket']}: Profit {profit_points:.2f} points, "
                                        f"Entry Time: {trade['entry_time']}, Timeframe: {trade['timeframe']}")
                return "\n".join(history_lines)
            return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"

        if cmd == "fetch_suretrend_history" and len(cmd_parts) >= 2:
            symbol = cmd_parts[1].upper()
            if symbol in self.symbols:
                history_lines = [f"SureTrend Trade History for {symbol} (Last 5):"]
                trades = self.suretrend_history[symbol][-5:]
                if not trades:
                    history_lines.append("  No SureTrend trades recorded.")
                for trade in trades:
                    profit_points = self.convert_to_points(trade['profit'], symbol)
                    history_lines.append(f"  {trade['type']} Ticket {trade['ticket']}: Profit {profit_points:.2f} points, "
                                        f"Entry Time: {trade['entry_time']}, Timeframe: {trade['timeframe']}")
                return "\n".join(history_lines)
            return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"

        if cmd == "set_lot_size" and len(cmd_parts) >= 2:
            try:
                new_size = float(cmd_parts[1])
                if new_size <= 0:
                    return "Lot size must be positive."
                self.lot_size = new_size
                return f"Default lot size updated to {new_size:.2f}."
            except ValueError:
                return f"Invalid lot size '{cmd_parts[1]}'. Please provide a numeric value."

        if cmd == "set_daily_profit_limit" and len(cmd_parts) >= 2:
            new_limit = float(cmd_parts[1])
            self.daily_max_profit = new_limit
            return f"Daily profit limit set to {new_limit:.2f} points."

        if cmd == "set_breakeven" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            value = float(cmd_parts[2])
            if tf:
                self.breakeven_configs[tf] = value
                return f"Breakeven trigger set to {value:.2f} points for {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe: {cmd_parts[1]}. Available timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "set_trailing_stop" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            value = float(cmd_parts[2])
            if tf:
                self.trailing_stop_configs[tf] = value
                return f"Trailing stop distance set to {value:.2f} points for {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe: {cmd_parts[1]}. Available timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "set_trailing_delay" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            value = float(cmd_parts[2])
            if tf:
                self.trailing_delay_configs[tf] = value
                return f"Trailing stop activation delay set to {value:.2f} points for {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe: {cmd_parts[1]}. Available timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "set_cooldown" and len(cmd_parts) >= 2:
            new_cooldown = int(cmd_parts[1])
            self.signal_cooldown = new_cooldown
            return f"Signal cooldown set to {new_cooldown} seconds."

        if cmd in ["m1_exit", "m5_exit", "m15_exit", "m30_exit", "h1_exit", "h4_exit"] and len(cmd_parts) >= 3:
            tf_str = cmd.split('_')[0].upper()
            state = cmd_parts[1].lower()
            symbol = cmd_parts[2].upper()
            if tf_str in self.timeframe_configs and state in ["on", "off"] and symbol in self.symbols:
                timeframe = self.timeframe_configs[tf_str]
                self.ma_exit_enabled[symbol][timeframe] = state == "on"
                return f"{tf_str} exit signals {'enabled' if self.ma_exit_enabled[symbol][timeframe] else 'disabled'} for {symbol}."
            return f"Invalid timeframe '{tf_str}', state '{state}', or symbol '{symbol}'. Usage: {cmd} <on/off> <symbol>"

        if cmd == "enable_volatility" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            symbol = cmd_parts[2].upper()
            if tf and symbol in self.symbols:
                self.volatility_check_enabled[symbol][tf] = True
                return f"Volatility check enabled for {symbol} on {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe '{cmd_parts[1]}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "disable_volatility" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            symbol = cmd_parts[2].upper()
            if tf and symbol in self.symbols:
                self.volatility_check_enabled[symbol][tf] = False
                return f"Volatility check disabled for {symbol} on {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe '{cmd_parts[1]}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "enable_psar_filter" and len(cmd_parts) >= 4:
            mon_tf = self.parse_timeframe(cmd_parts[1])
            psar_tf = self.parse_timeframe(cmd_parts[2])
            symbol = cmd_parts[3].upper()
            if mon_tf and psar_tf and symbol in self.symbols:
                self.psar_filter_enabled[symbol][mon_tf] = True
                self.psar_filter_timeframe[symbol][mon_tf] = psar_tf
                return f"PSAR filter enabled for {symbol} on {self.get_timeframe_name(mon_tf)} using {self.get_timeframe_name(psar_tf)}."
            return f"Invalid monitoring timeframe '{cmd_parts[1]}' or PSAR timeframe '{cmd_parts[2]}' or symbol '{symbol}'."

        if cmd == "disable_psar_filter" and len(cmd_parts) >= 3:
            tf = self.parse_timeframe(cmd_parts[1])
            symbol = cmd_parts[2].upper()
            if tf and symbol in self.symbols:
                self.psar_filter_enabled[symbol][tf] = False
                return f"PSAR filter disabled for {symbol} on {self.get_timeframe_name(tf)}."
            return f"Invalid timeframe '{cmd_parts[1]}' or symbol '{symbol}'. Timeframes: {', '.join(self.timeframe_configs.keys())}"

        if cmd == "enable_dynamic_management":
            self.dynamic_management_enabled = True
            return f"Dynamic position management enabled for scope {', '.join(scope)}."

        if cmd == "disable_dynamic_management":
            self.dynamic_management_enabled = False
            return f"Dynamic position management disabled for scope {', '.join(scope)}."

        if cmd == "enable_suretrend_automation":
            self.suretrend_automation_enabled = True
            return f"SureTrend automation enabled for scope {', '.join(scope)}."

        if cmd == "disable_suretrend_automation":
            self.suretrend_automation_enabled = False
            return f"SureTrend automation disabled for scope {', '.join(scope)}."

        if cmd == "enable_grid_trading":
            self.grid_trading_enabled = True
            return f"Grid trading enabled for scope {', '.join(scope)}."

        if cmd == "disable_grid_trading":
            self.grid_trading_enabled = False
            return f"Grid trading disabled for scope {', '.join(scope)}."

        if cmd == "enable_primary_strategy":
            self.primary_strategy_enabled = True
            return f"Primary strategy enabled for scope {', '.join(scope)}."

        if cmd == "disable_primary_strategy":
            self.primary_strategy_enabled = False
            return f"Primary strategy disabled for scope {', '.join(scope)}."

        if cmd == "enable_exit_signals":
            self.exit_signals_enabled = True
            return f"Exit signals enabled for scope {', '.join(scope)}."

        if cmd == "disable_exit_signals":
            self.exit_signals_enabled = False
            return f"Exit signals disabled for scope {', '.join(scope)}."

        if cmd == "config_ma" and len(cmd_parts) >= 5:
            tf = self.parse_timeframe(cmd_parts[1])
            ma_type = cmd_parts[2].lower()
            period = int(cmd_parts[3])
            symbol = cmd_parts[4].upper()
            if tf and symbol in self.symbols and ma_type in ['fast', 'slow', 'exit_fast', 'exit_slow']:
                self.ma_configs[tf][ma_type] = period
                return f"{ma_type.capitalize()} MA set to {period} for {symbol} on {self.get_timeframe_name(tf)}."
            return "Usage: /config_ma <timeframe> <fast/slow/exit_fast/exit_slow> <period> <symbol>"

        if cmd == "config_ma_bulk" and len(cmd_parts) >= 3:
            configs = " ".join(cmd_parts[1:]).split(';')
            updated = []
            for config in configs:
                parts = config.strip().split()
                if len(parts) != 4:
                    continue
                tf, ma_type, period, symbol = parts[0], parts[1].lower(), int(parts[2]), parts[3].upper()
                tf_val = self.parse_timeframe(tf)
                if tf_val and symbol in self.symbols and ma_type in ['fast', 'slow', 'exit_fast', 'exit_slow']:
                    self.ma_configs[tf_val][ma_type] = period
                    updated.append(f"{ma_type}={period} on {tf} for {symbol}")
            return f"Bulk MA config updated: {', '.join(updated)}" if updated else "No valid configs provided."

        if cmd == "setparams":
            return self.handle_position_params(cmd_parts)

        if cmd == "gen_report":
            try:
                if len(cmd_parts) < 2:
                    return "Usage: gen_report --ticket <ticket> | --symbol <symbol> | --daily"
                
                if cmd_parts[1] == "--ticket" and len(cmd_parts) >= 3:
                    return self.generate_trade_report(ticket=int(cmd_parts[2]))
                elif cmd_parts[1] == "--symbol" and len(cmd_parts) >= 3:
                    return self.generate_trade_report(symbol=cmd_parts[2].upper())
                elif cmd_parts[1] == "--daily":
                    return self.generate_trade_report(daily=True)
                else:
                    return "Invalid report type. Use --ticket, --symbol, or --daily"
            except Exception as e:
                return f"Error generating report: {str(e)}"

        if cmd == "status":
            status_lines = [f"Trading System Status for Scope {', '.join(scope)}:"]
            status_lines.append(f"Trading Allowed: {', '.join([f'{sym}: {self.trading_allowed[sym]}' for sym in scope])}")
            status_lines.append(f"Daily Profit: {', '.join([f'{sym}: {self.convert_to_points(self.daily_profit[sym], sym):.2f} points' for sym in scope])}")
            status_lines.append(f"Open Positions: {sum(len(self.positions[sym]) for sym in scope)}")
            status_lines.append("Strategy States:")
            status_lines.append(f"  Primary: {'Semi-Auto' if self.primary_strategy_semi_auto else 'Full Auto' if self.primary_strategy_enabled else 'Disabled'}")
            status_lines.append(f"  SureTrend: {'Semi-Auto' if self.suretrend_semi_auto else 'Full Auto' if self.suretrend_automation_enabled else 'Disabled'}")
            status_lines.append(f"  Grid: {'Semi-Auto' if self.grid_semi_auto else 'Full Auto' if self.grid_trading_enabled else 'Disabled'}")
            status_lines.append(f"  Momentum: {'Semi-Auto' if self.momentum_semi_auto else 'Full Auto' if self.momentum_automation_enabled else 'Disabled'}")
            status_lines.append(f"Dynamic Management: {self.dynamic_management_enabled}")
            status_lines.append(f"Exit Signals: {self.exit_signals_enabled}")
            status_lines.append(f"Lot Size: {self.lot_size:.2f}")
            status_lines.append(f"Daily Profit Limit: {self.daily_max_profit:.2f} points")
            status_lines.append(f"Simulation Mode: {self.simulate}")
            for symbol in scope:
                for tf in self.timeframes:
                    tf_name = self.get_timeframe_name(tf)
                    if self.suretrend_conditions_met[symbol][tf]['buy']:
                        status_lines.append(f"SureTrend BUY conditions met for {symbol} on {tf_name}")
                    elif self.suretrend_conditions_met[symbol][tf]['sell']:
                        status_lines.append(f"SureTrend SELL conditions met for {symbol} on {tf_name}")
            return "\n".join(status_lines)

        if cmd == "help":
            help_lines = [
                "🤖 Trading Bot Command Guide",
                "",
                "📈 Strategy Management:",
                "  enable_primary_strategy/disable_primary_strategy - Control primary strategy",
                "  enable_suretrend_automation/disable_suretrend_automation - Control SureTrend",
                "  enable_grid_trading/disable_grid_trading - Control grid trading",
                "  enable_momentum_automation/disable_momentum_automation - Control momentum",
                "  enable_hfscalper/disable_hfscalper - Control HFScalper strategy",
                "",
                "🔄 Semi-Auto Mode:",
                "  enable_primary_semi_auto/disable_primary_semi_auto - Control primary semi-auto",
                "  enable_suretrend_semi_auto/disable_suretrend_semi_auto - Control SureTrend semi-auto",
                "  enable_grid_semi_auto/disable_grid_semi_auto - Control grid semi-auto",
                "  enable_momentum_semi_auto/disable_momentum_semi_auto - Control momentum semi-auto",
                "  enable_hfscalper_semi_auto/disable_hfscalper_semi_auto - Control HFScalper semi-auto",
                "",
                "⚙️ Strategy Configuration:",
                "  set_hfscalper_min_momentum <value> - Set minimum momentum threshold",
                "  set_hfscalper_volatility <value> - Set volatility threshold",
                "  set_hfscalper_tp <points> - Set take profit in points",
                "  set_hfscalper_psar_step <value> - Set PSAR step",
                "  set_hfscalper_psar_max <value> - Set PSAR maximum",
                "  enable_hfscalper_psar/disable_hfscalper_psar - Control HFScalper PSAR filter",
                "",
                "👥 Account Management:",
                "  add_account <name> <login> <password> <server> - Add trading account",
                "  switch_account <name> - Switch to specified account",
                "  enable_sync/disable_sync - Control multi-account synchronization",
                "  list_accounts - Show configured accounts",
                "",
                "💹 Basic Trading Commands:",
                "  buy_market <timeframe> <symbol> - Place market buy order",
                "  sell_market <timeframe> <symbol> - Place market sell order",
                "  m1b/m5b/.../h4b <symbol> - Buy with strategy checks",
                "  m1s/m5s/.../h4s <symbol> - Sell with strategy checks",
                "  m1b0/m5b0/.../h4b0 <symbol> - Immediate buy without checks",
                "  m1s0/m5s0/.../h4s0 <symbol> - Immediate sell without checks",
                "",
                "📊 TP-Based Trading:",
                "  <points>b/s <symbol> [timeframe] - Trade with TP on MA crossover",
                "  <points>b0/s0 <symbol> [timeframe] - Immediate trade with TP",
                "  Valid points: 50, 100, 150, 200, 250, 300, 350, 400, 500, 600, 800, 1000, 2000",
                "",
                "🎯 Position Management:",
                "  close <ticket> - Close specific position",
                "  close_all - Close all open positions",
                "  close_partial <symbol> <ticket> <percent> - Close part of position",
                "  add_to_position <symbol> <ticket> <lots> - Add to position",
                "  set_sl <symbol> <ticket> <value> - Set stop loss",
                "  set_tp <symbol> <ticket> <value> - Set take profit",
                "  modify <symbol> <ticket> <sl/tp> <value> - Modify SL/TP",
                "  setparams <ticket> <sl_points> <tp_points> <trail_stop> <trail_delay> <ma_exit> - Set position parameters",
                "",
                "📈 Signal Optimization:",
                "  optimize_signals - Enable signal optimization",
                "  disable_signal_optimization - Disable signal optimization",
                "  set_signal_interval <seconds> - Set signal check interval",
                "  get_signal_stats [symbol] [timeframe] - Get signal performance",
                "  enable_realtime_signals/disable_realtime_signals - Control real-time signals",
                "  set_signal_threshold <value> - Set signal quality threshold",
                "  enable_signal_alerts/disable_signal_alerts - Control signal alerts",
                "  enable_signal_logging/disable_signal_logging - Control signal logging",
                "",
                "⚙️ Risk Management:",
                "  set_lot_size <value> - Set default lot size",
                "  set_daily_profit_limit <value> - Set daily profit limit",
                "  set_breakeven <timeframe> <points> - Set breakeven trigger",
                "  set_trailing_stop <timeframe> <points> - Set trailing stop",
                "  set_trailing_delay <timeframe> <points> - Set trailing activation",
                "  set_cooldown <seconds> - Set signal cooldown",
                "",
                "🔍 Analysis & Filters:",
                "  enable_volatility/disable_volatility <timeframe> <symbol> - Control volatility check",
                "  enable_psar_filter/disable_psar_filter <timeframe> <symbol> - Control PSAR filter",
                "  enable_dynamic_management/disable_dynamic_management - Control dynamic management",
                "  enable_exit_signals/disable_exit_signals - Control exit signals",
                "  m1_exit/m5_exit/.../h4_exit <on/off> <symbol> - Control MA exits",
                "",
                "📊 Moving Average Configuration:",
                "  config_ma <timeframe> <type> <period> <symbol> - Configure single MA",
                "  config_ma_bulk <configs> - Bulk configure MAs",
                "  Types: fast, slow, exit_fast, exit_slow",
                "",
                "📈 Monitoring & Reports:",
                "  status - Show system status",
                "  metrics - Show detailed metrics",
                "  history - Show recent trade history",
                "  daily_history <symbol> - Show today's trades",
                "  fetch_suretrend_history <symbol> - Show SureTrend trades",
                "  strategy_history <strategy> <symbol> - Show strategy-specific trades",
                "  fetch_chart <symbol> <timeframe> - Generate chart",
                "  gen_report --ticket <ticket> - Generate ticket report",
                "  gen_report --symbol <symbol> - Generate symbol report",
                "  gen_report --daily - Generate daily report",
                "",
                "💬 Trade Information:",
                "  comment <ticket> <text> - Add comment to position",
                "  reason <ticket> <text> - Update trade reason",
                "",
                "🔒 Trading Lock Commands:",
                "  unlock_trading <password> - Unlock trading (admin only)",
                "  trading_status - Check current trading lock status",
                "",
                "⚡ Quick Commands:",
                "  cd <symbol> | .. - Set/reset context symbol",
                "  stop - Stop trading",
                "  start - Start trading",
                "  resume <symbol> - Resume symbol trading",
                "  yes - Confirm pending semi-auto trade",
                "  no - Reject pending semi-auto trade",
                "  exit - Exit the program"
            ]
            return "\n".join(help_lines)

        if cmd == "fetch_chart" and len(cmd_parts) >= 3:
            try:
                symbol = cmd_parts[1].upper()
                timeframe = cmd_parts[2].upper()
                
                if symbol not in self.symbols:
                    return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"
                
                if timeframe not in self.timeframe_configs:
                    return f"Invalid timeframe: {timeframe}. Available timeframes: {', '.join(self.timeframe_configs.keys())}"
                
                result = self.fetch_chart(symbol, timeframe)
                return result
            except Exception as e:
                self.logger.error(f"Error in fetch_chart command: {str(e)}")
                return f"Error generating chart: {str(e)}"

        if cmd == "manual_tp" and len(cmd_parts) >= 5:
            symbol = cmd_parts[1].upper()
            timeframe = self.parse_timeframe(cmd_parts[2])
            direction = cmd_parts[3].upper()
            tp_points = int(cmd_parts[4])
            return self.execute_manual_tp_trade(symbol, timeframe, direction, tp_points)

        if cmd == "strategy_history" and len(cmd_parts) >= 3:
            strategy = cmd_parts[1].lower()
            symbol = cmd_parts[2].upper()
            return self.fetch_strategy_history(strategy, symbol)

        if cmd == "momentum" and len(cmd_parts) >= 3:
            symbol = cmd_parts[1].upper()
            timeframe = self.parse_timeframe(cmd_parts[2])
            return self.execute_momentum_strategy(symbol, timeframe)

        if cmd == "enable_primary_semi_auto":
            self.primary_strategy_semi_auto = True
            return f"Primary strategy semi-automated mode enabled for scope {', '.join(scope)}."

        if cmd == "disable_primary_semi_auto":
            self.primary_strategy_semi_auto = False
            return f"Primary strategy semi-automated mode disabled for scope {', '.join(scope)}."

        if cmd == "enable_suretrend_semi_auto":
            self.suretrend_semi_auto = True
            return f"SureTrend semi-automated mode enabled for scope {', '.join(scope)}."

        if cmd == "disable_suretrend_semi_auto":
            self.suretrend_semi_auto = False
            return f"SureTrend semi-automated mode disabled for scope {', '.join(scope)}."

        if cmd == "enable_grid_semi_auto":
            self.grid_semi_auto = True
            return f"Grid trading semi-automated mode enabled for scope {', '.join(scope)}."

        if cmd == "disable_grid_semi_auto":
            self.grid_semi_auto = False
            return f"Grid trading semi-automated mode disabled for scope {', '.join(scope)}."

        if cmd == "enable_momentum_semi_auto":
            self.momentum_semi_auto = True
            return f"Momentum strategy semi-automated mode enabled for scope {', '.join(scope)}."

        if cmd == "disable_momentum_semi_auto":
            self.momentum_semi_auto = False
            return f"Momentum strategy semi-automated mode disabled for scope {', '.join(scope)}."

        if cmd == "fetch_chart":
            try:
                if len(cmd_parts) < 3:
                    return "Usage: fetch_chart <symbol> <timeframe>"
                
                symbol = cmd_parts[1].upper()
                timeframe = cmd_parts[2].upper()
                
                if symbol not in self.symbols:
                    return f"Invalid symbol: {symbol}. Available symbols: {', '.join(self.symbols)}"
                
                if timeframe not in self.timeframe_configs:
                    return f"Invalid timeframe: {timeframe}. Available timeframes: {', '.join(self.timeframe_configs.keys())}"
                
                return self.fetch_chart(symbol, timeframe)
            except Exception as e:
                self.logger.error(f"Error in fetch_chart command: {str(e)}")
                return f"Error generating chart: {str(e)}"

        return f"Unknown command: {command}. Type 'help' for available commands."

    def trade_execution_loop(self, symbol, timeframe):
            """Enhanced trade execution loop with trading lock checks."""
            check_interval = self.timeframe_intervals[timeframe]
            min_check_interval = 1
            last_sync_time = datetime.now()
            sync_interval = 30
            last_drawdown_check = datetime.now()
            drawdown_check_interval = 60  # Check drawdown every minute
            last_market_check = datetime.now()  # Initialize last_market_check
            
            # Add at the beginning of the loop
            update_interval = 1  # Update dashboard every second
            last_update = datetime.now()
            
            while True:
                try:
                    current_time = datetime.now()
                    
                    # Update dashboard periodically
                    if (current_time - last_update).total_seconds() >= update_interval:
                        self.display_dashboard()
                        self.update_status_line()
                        last_update = current_time
                    
                    # ... rest of your existing loop code ...
            try:
                current_time = datetime.now()
                
                # Check if trading is locked
                if self.trading_locked:
                    self.logger.warning(f"Trading is locked: {self.trading_lock_reason}")
                    time.sleep(60)  # Check every minute if lock is removed
                    continue
                
                # Periodic drawdown check
                if (current_time - last_drawdown_check).total_seconds() >= drawdown_check_interval:
                    if self.check_drawdown():
                        continue
                    last_drawdown_check = current_time
                
                # Check daily profit/loss limits
                total_daily_profit = sum(self.convert_to_points(self.daily_profit[s], s) for s in self.symbols)
                if total_daily_profit >= self.daily_max_profit:
                    self.lock_trading(f"Daily profit target reached: {total_daily_profit:.2f} points")
                    continue
                
                if total_daily_profit <= self.max_daily_loss:
                    self.lock_trading(f"Maximum daily loss reached: {total_daily_profit:.2f} points")
                    continue
                
                # Check market status periodically
                if (current_time - last_market_check).total_seconds() >= self.market_check_interval:
                    if not self.is_market_open(symbol):
                        self.logger.info(f"[{symbol}] Market is closed, sleeping for {self.market_closed_sleep} seconds")
                        time.sleep(self.market_closed_sleep)
                        last_market_check = current_time
                        continue
                    last_market_check = current_time
                
                # Sync with MT5 periodically
                if not self.simulate and (current_time - last_sync_time).total_seconds() >= sync_interval:
                    if not self.ensure_mt5_connection():
                        self.logger.warning(f"[{symbol} {self.get_timeframe_name(timeframe)}] MT5 connection failed, retrying...")
                        time.sleep(5)
                        continue
                    self.sync_positions_with_mt5()
                    last_sync_time = current_time
                
                # Calculate time since last check
                time_since_last_check = (current_time - self.last_check_times[symbol][timeframe]).total_seconds()
                
                # Determine if we should check signals
                should_check = time_since_last_check >= check_interval
                
                if should_check:
                    self.logger.debug(f"[{symbol} {self.get_timeframe_name(timeframe)}] Checking signals after {time_since_last_check:.0f} seconds")
                    self.last_check_times[symbol][timeframe] = current_time
                    
                    # Skip if trading is paused or daily profit reached
                    if not self.trading_allowed[symbol] or self.convert_to_points(self.daily_profit[symbol], symbol) >= self.daily_max_profit:
                        time.sleep(min_check_interval)
                        continue
                    
                    # Get latest data
                    df = self.get_or_update_rates(symbol, timeframe)
                    if df is None or len(df) < 10:
                        time.sleep(min_check_interval)
                        continue
                    
                    # Rest of your existing trade execution logic...
                    # [Rest of the code remains unchanged]
                    
                # Sleep for a short time before next check
                sleep_time = min(min_check_interval, check_interval - time_since_last_check if not should_check else min_check_interval)
                if sleep_time > 0:
                    time.sleep(sleep_time)
                    
            except Exception as e:
                self.logger.error(f"[{symbol} {self.get_timeframe_name(timeframe)}] Error in trade execution loop: {str(e)}", exc_info=True)
                time.sleep(min_check_interval)
            try:
                current_time = datetime.now()
                
                # Sync with MT5 periodically
                if not self.simulate and (current_time - last_sync_time).total_seconds() >= sync_interval:
                    if not self.ensure_mt5_connection():
                        self.logger.warning(f"[{symbol} {self.get_timeframe_name(timeframe)}] MT5 connection failed, retrying...")
                        time.sleep(5)
                        continue
                    self.sync_positions_with_mt5()
                    last_sync_time = current_time
                
                # Calculate time since last check
                time_since_last_check = (current_time - self.last_check_times[symbol][timeframe]).total_seconds()
                
                # Determine if we should check signals
                should_check = time_since_last_check >= check_interval
                
                if should_check:
                    self.logger.debug(f"[{symbol} {self.get_timeframe_name(timeframe)}] Checking signals after {time_since_last_check:.0f} seconds")
                    self.last_check_times[symbol][timeframe] = current_time
                    
                    # Skip if trading is paused or daily profit reached
                    if not self.trading_allowed[symbol] or self.convert_to_points(self.daily_profit[symbol], symbol) >= self.daily_max_profit:
                        self.logger.info(f"[{symbol} {self.get_timeframe_name(timeframe)}] Trading paused: Daily profit reached or trading disabled.")
                        time.sleep(min_check_interval)
                        continue

                    # Skip if market is closed
                    if not self.is_market_open(symbol):
                        self.logger.info(f"[{symbol}] Market is closed, sleeping until open.")
                        time.sleep(60)  # Check every minute if market is open
                        continue

                    # Get latest data
                    df = self.get_or_update_rates(symbol, timeframe)
                    if df is None or len(df) < 10:
                        self.logger.warning(f"[{symbol} {self.get_timeframe_name(timeframe)}] Insufficient or no data retrieved.")
                        time.sleep(min_check_interval)
                        continue

                    # Check for existing positions on this timeframe
                    timeframe_positions = [pos for pos in self.positions[symbol].values() if pos['timeframe'] == timeframe]
                    if not timeframe_positions:  # Only check for new signals if no position exists for this timeframe
                        # Check if enough time has passed since last signal
                        time_since_last_signal = (current_time - self.last_signal_times[symbol][timeframe]).total_seconds()
                        if time_since_last_signal < self.signal_cooldown:
                            self.logger.debug(f"[{symbol} {self.get_timeframe_name(timeframe)}] Signal cooldown active for {self.signal_cooldown - time_since_last_signal:.0f} more seconds")
                            time.sleep(min_check_interval)
                            continue

                        current_price = df['close'].iloc[-1]
                        tick = mt5.symbol_info_tick(symbol) if not self.simulate else None
                        bid, ask = (tick.bid, tick.ask) if tick else (current_price, current_price + 0.0005)

                        # Check volatility if enabled
                        if self.volatility_check_enabled[symbol][timeframe]:
                            volatility_state = self.check_volatility(df)
                            if volatility_state == "high_volatility":
                                self.logger.info(f"[{symbol} {self.get_timeframe_name(timeframe)}] High volatility detected, skipping trade.")
                                time.sleep(min_check_interval)
                                continue

                        # Check PSAR filter if enabled
                        if self.psar_filter_enabled[symbol][timeframe]:
                            psar_df = self.get_or_update_rates(symbol, self.psar_filter_timeframe[symbol][timeframe])
                            if psar_df is not None and not psar_df.empty:
                                latest_psar = psar_df['psar'].iloc[-1]
                                if current_price < latest_psar:
                                    self.logger.info(f"[{symbol} {self.get_timeframe_name(timeframe)}] PSAR filter blocked signal")
                                    time.sleep(min_check_interval)
                                    continue

                        # Check all strategy signals
                        signals = []
                        if self.primary_strategy_enabled:
                            primary_signal, primary_message, primary_time = self.check_primary_signal(df, timeframe, symbol)
                            if primary_signal:
                                signals.append(("primary", primary_signal, primary_message, primary_time))

                        if self.suretrend_automation_enabled:
                            existing_suretrend_trades = [pos for pos in self.positions[symbol].values() if pos['strategy'] == 'suretrend']
                            if not existing_suretrend_trades:
                                suretrend_signal, suretrend_message, suretrend_time = self.check_suretrend_signal(df, timeframe, symbol)
                                if suretrend_signal:
                                    signals.append(("suretrend", suretrend_signal, suretrend_message, suretrend_time))

                        if self.grid_trading_enabled:
                            grid_signal, grid_message, grid_time = self.check_grid_signal(df, timeframe, symbol)
                            if grid_signal:
                                signals.append(("grid", grid_signal, grid_message, grid_time))

                        if self.momentum_automation_enabled:
                            momentum_signal, momentum_message, momentum_time = self.check_momentum_signal(df, timeframe, symbol)
                            if momentum_signal:
                                signals.append(("momentum", momentum_signal, momentum_message, momentum_time))

                        # Add HFScalper strategy check
                        if self.hfscalper_enabled and timeframe == mt5.TIMEFRAME_M1:  # Only on M1 timeframe
                            hfscalper_signal, hfscalper_message, hfscalper_time = self.check_hfscalper_signal(df, timeframe, symbol)
                            if hfscalper_signal:
                                signals.append(("hfscalper", hfscalper_signal, hfscalper_message, hfscalper_time))

                        # Process signals
                        for strategy, signal, message, signal_time in signals:
                            order_type = mt5.ORDER_TYPE_BUY if signal == "BUY" else mt5.ORDER_TYPE_SELL
                            entry_price = ask if signal == "BUY" else bid
                            
                            # Check if strategy is in semi-automated mode
                            is_semi_auto = (
                                (strategy == "primary" and self.primary_strategy_semi_auto) or
                                (strategy == "suretrend" and self.suretrend_semi_auto) or
                                (strategy == "grid" and self.grid_semi_auto) or
                                (strategy == "momentum" and self.momentum_semi_auto) or
                                (strategy == "hfscalper" and self.hfscalper_semi_auto)
                            )
                            
                            if is_semi_auto:
                                self.prompt_trade_confirmation(symbol, timeframe, signal, f"[SEMI-AUTO {strategy.upper()}] {message}", signal_time)
                            else:
                                success, position = self.open_position(order_type, entry_price, signal_time, message, timeframe, symbol, strategy)
                                if success:
                                    self.last_signal_times[symbol][timeframe] = current_time

                    # Manage existing positions
                    with self.command_lock:
                        for ticket, position in list(self.positions[symbol].items()):
                            df_pos = self.get_or_update_rates(symbol, position['timeframe'])
                            if df_pos is None:
                                continue
                            
                            current_price = df_pos['close'].iloc[-1]
                            
                            # Check SL/TP
                            if self.check_sl_tp(position, current_price):
                                continue
                            
                            # Check exit signals
                            if self.check_exit_conditions(position, df_pos):
                                continue
                            
                            # Position management
                            if position['strategy'] == 'hfscalper':
                                self.handle_hfscalper_trade(symbol, df_pos)
                            else:
                                self.manage_position(position, current_price, df_pos)

                # Sleep for a short time before next check
                sleep_time = min(min_check_interval, check_interval - time_since_last_check if not should_check else min_check_interval)
                if sleep_time > 0:
                    time.sleep(sleep_time)

            except Exception as e:
                self.logger.error(f"[{symbol} {self.get_timeframe_name(timeframe)}] Error in trade execution loop: {str(e)}", exc_info=True)
                time.sleep(min_check_interval)

    def check_sl_tp(self, position, current_price):
        """Check if position should be closed due to SL/TP"""
        sl = position['sl']
        tp = position['tp']
        if (position['type'] == mt5.ORDER_TYPE_BUY and (current_price <= sl or (tp > 0 and current_price >= tp))) or \
           (position['type'] == mt5.ORDER_TYPE_SELL and (current_price >= sl or (tp > 0 and current_price <= tp))):
            return self.close_position(position, "SL/TP Hit")
        return False

    def check_exit_conditions(self, position, df):
        """Check if position should be closed due to exit signals"""
        symbol = position['symbol']
        tf_key = position['timeframe'] if isinstance(position['timeframe'], str) else self.get_timeframe_name(position['timeframe'])
        
        if self.exit_signals_enabled and self.ma_exit_enabled[symbol].get(tf_key, False):
            should_exit, exit_reason = self.check_exit_signal(position, df)
            if should_exit:
                return self.close_position(position, exit_reason)
        return False

    def check_ma_crossover(self, df):
        if len(df) < max(self.ma_configs.values(), key=lambda x: x['slow'])['slow'] + 1:
            return False
        # Use a default timeframe if df.name isn't set correctly; assume M1 for simulation
        timeframe = df.name[1] if hasattr(df, 'name') and isinstance(df.name, tuple) and len(df.name) > 1 else mt5.TIMEFRAME_M1
        df['fast_ma'] = df['close'].rolling(window=self.ma_configs[timeframe]['fast']).mean()
        df['slow_ma'] = df['close'].rolling(window=self.ma_configs[timeframe]['slow']).mean()
        latest = df.iloc[-1]
        prev = df.iloc[-2]
        return (latest['fast_ma'] > latest['slow_ma'] and prev['fast_ma'] <= prev['slow_ma']) or \
               (latest['fast_ma'] < latest['slow_ma'] and prev['fast_ma'] >= prev['slow_ma'])

    def is_market_open(self, symbol):
        if self.simulate:
            return True
        info = mt5.symbol_info(symbol)
        if not info or not info.trade_mode:
            return False
        now = datetime.now()
        weekday = now.weekday()
        return weekday < 5 and info.session_open > 0

    def sync_positions_with_mt5(self):
        if self.sync_enabled and self.current_account:
            positions = mt5.positions_get()
            if positions:
                for pos in positions:
                    symbol = pos.symbol
                    if symbol in self.symbols:
                        ticket = pos.ticket
                        if ticket not in self.positions[symbol]:
                            self.positions[symbol][ticket] = {
                                'ticket': ticket,
                                'type': pos.type,
                                'entry_price': pos.price_open,
                                'lot_size': pos.volume,
                                'sl': pos.sl,
                                'tp': pos.tp,
                                'timeframe': mt5.TIMEFRAME_M1,  # Default, adjust as needed
                                'strategy': 'external',
                                'entry_time': datetime.fromtimestamp(pos.time).strftime('%Y-%m-%d %H:%M:%S.%f'),
                                'comments': pos.comment,
                                'profit': pos.profit
                            }

    def run(self):
        if not self.initialize_mt5() and not self.simulate:
        
    def add_mock_trade_command(self):
        terminal_width = shutil.get_terminal_size().columns
        half_width = terminal_width // 2

        def format_duration(seconds):
            return str(timedelta(seconds=int(seconds)))

        def display_trade_progress(symbol, entry_price, trade_type, lot_size):
            entry_time = datetime.now()
            pbar = tqdm(total=100, ncols=terminal_width, bar_format='{desc}')
            
            try:
                while True:
                    current_time = datetime.now()
                    duration = (current_time - entry_time).total_seconds()
                    
                    # Simulate price movement
                    price_change = (random.random() - 0.5) * 0.001
                    current_price = entry_price * (1 + price_change)
                    
                    # Calculate PnL in points
                    pnl_points = (current_price - entry_price) / self.point[symbol]
                    if trade_type == "SELL":
                        pnl_points = -pnl_points
                    
                    # Create progress bar segments
                    if pnl_points >= 0:
                        left_progress = "▢" * half_width
                        right_progress = "█" * min(int(pnl_points), half_width)
                    else:
                        left_progress = "█" * min(int(-pnl_points), half_width)
                        right_progress = "▢" * half_width

                    # Format trade info
                    trade_info = (
                        f"{symbol} | {trade_type} | {lot_size:.2f} lots | "
                        f"Entry: {entry_price:.5f} | Current: {current_price:.5f} | "
                        f"PnL: {pnl_points:.1f} pts | "
                        f"Duration: {format_duration(duration)}"
                    )
                    
                    # Update progress bar
                    pbar.set_description_str(
                        f"{trade_info}\n{left_progress}|{right_progress}"
                    )
                    pbar.update(0)
                    
                    time.sleep(0.1)  # Update every 100ms
                    
            except KeyboardInterrupt:
                pbar.close()
                return f"Mock trade closed after {format_duration(duration)}"

        return display_trade_progress

    def mock_trade(self, symbol, trade_type, lot_size=0.01):
        """Open a mock trade with real-time progress display"""
        if symbol not in self.symbols:
            return f"Invalid symbol: {symbol}"
        
        try:
            # Get current market price
            if self.simulate:
                current_price = 1900.00  # Mock price for simulation
            else:
                tick = mt5.symbol_info_tick(symbol)
                if not tick:
                    return f"Failed to get price for {symbol}"
                current_price = tick.ask if trade_type == "BUY" else tick.bid
            
            # Create and start progress display
            progress_display = self.add_mock_trade_command()
            result = progress_display(symbol, current_price, trade_type, lot_size)
            return result
            
        except Exception as e:
            self.logger.error(f"Error in mock trade: {str(e)}")
            return f"Error: {str(e)}"
            self.logger.error("Failed to start trading system due to MT5 initialization failure.")
            return

        telegram_thread = threading.Thread(target=self.telegram_listener, daemon=True)
        telegram_thread.start()
        self.threads.append(telegram_thread)

        terminal_thread = threading.Thread(target=self.terminal_listener, daemon=True)
        terminal_thread.start()
        self.threads.append(terminal_thread)

        for symbol in self.symbols:
            for timeframe in self.timeframes:
                thread = threading.Thread(
                    target=self.trade_execution_loop,
                    args=(symbol, timeframe),
                    daemon=True
                )
                thread.start()
                self.threads.append(thread)
                if symbol not in self.symbol_terminal_threads:
                    self.symbol_terminal_threads[symbol] = []
                self.symbol_terminal_threads[symbol].append(thread)

        self.logger.info("Trading system started.")
        for thread in self.threads:
            thread.join()

    def check_connections(self):
        """Check and report connection status."""
        mt5_status = "✅ Connected" if self.mt5_connected else "❌ Disconnected"
        telegram_status = "✅ Connected" if self.telegram_connected else "❌ Disconnected"
        
        status_message = (
            f"🔌 Connection Status:\n"
            f"MT5: {mt5_status}\n"
            f"Telegram: {telegram_status}\n"
        )
        
        self.logger.info(status_message)
        return self.mt5_connected and self.telegram_connected

    def create_progress_bar(filled, total, width=50, left_color='red', right_color='green', divider='|'):
        """Create a pretty progress bar with colors for negative/positive progress"""
        left_side = '█' * min(int(width/2), int((width/2) * (abs(min(filled, 0))/total)))
        right_side = '█' * min(int(width/2), int((width/2) * (max(filled, 0)/total)))
        
        # Pad with spaces
        left_side = left_side.ljust(int(width/2))
        right_side = right_side.ljust(int(width/2))
        
        # Add colors using ANSI escape codes
        colored_left = f"\033[91m{left_side}\033[0m"  # Red for negative
        colored_right = f"\033[92m{right_side}\033[0m"  # Green for positive
        
        return f"{colored_left}{divider}{colored_right}"

    def format_trade_info(self, position, current_price, symbol):
        """Format trade information with colors and symbols"""
        profit_points = self.convert_to_points(
            current_price - position['entry_price'] if position['type'] == mt5.ORDER_TYPE_BUY 
            else position['entry_price'] - current_price, 
            symbol
        )
        
        trade_type = "🟢 BUY" if position['type'] == mt5.ORDER_TYPE_BUY else "🔴 SELL"
        profit_color = "\033[92m" if profit_points >= 0 else "\033[91m"  # Green/Red
        
        info = (
            f"📊 {position['strategy'].upper()} Trade #{position['ticket']}\n"
            f"{'─'*50}\n"
            f"📈 {trade_type} {symbol} @ {position['entry_price']:.5f}\n"
            f"💰 Profit: {profit_color}{profit_points:.1f} pts\033[0m\n"
            f"🎯 Entry Time: {position['entry_time']}\n"
            f"⚡ Status: {self.get_position_status(position)}\n"
            f"📐 Lot Size: {position['lot_size']:.2f}\n"
            f"🛑 SL: {position['sl']:.5f}\n"
            f"✨ TP: {position['tp']:.5f}\n"
        )
        
        # Add progress bar
        max_points = abs(position['tp'] - position['entry_price']) / self.point[symbol]
        progress = self.create_progress_bar(profit_points, max_points)
        info += f"\n{progress}\n{'─'*50}\n"
        
        return info

    def get_position_status(self, position):
        """Get formatted position status with emoji"""
        if position.get('breakeven_triggered'):
            return "🔒 Breakeven Active"
        elif position.get('trailing_active'):
            return "🔄 Trailing Active"
        elif position.get('waiting_params'):
            return "⏳ Awaiting Parameters"
        return "🟡 Active"

    def display_trade_metrics(self):
        """Display pretty trade metrics"""
        header = "\n" + "═"*70 + "\n" + "🤖 TRADING SYSTEM METRICS" + "\n" + "═"*70 + "\n"
        try:
            self.update_terminal()
            self.update_status_line()  # Force status bar update
            return "Trade metrics displayed"
        except Exception as e:
            self.logger.error(f"Error displaying trade metrics: {str(e)}")
            return f"Error: {str(e)}"
             
        # Account info
        account_info = mt5.account_info() if not self.simulate else None
        balance = account_info.balance if account_info else self.initial_balance
        equity = account_info.equity if account_info else balance
        
        metrics = (
            f"💰 Balance: ${balance:.2f}\n"
            f"📈 Equity: ${equity:.2f}\n"
            f"🔄 Mode: {'🎮 Simulation' if self.simulate else '🌐 Live Trading'}\n"
            f"{'─'*70}\n"
        )
        
        # Daily profits
        metrics += "📊 Daily Profits:\n"
        for symbol in self.symbols:
            profit_points = self.convert_to_points(self.daily_profit[symbol], symbol)
            color = "\033[92m" if profit_points >= 0 else "\033[91m"
            progress = self.create_progress_bar(profit_points, self.daily_max_profit)
            metrics += f"{symbol}: {color}{profit_points:.1f}/{self.daily_max_profit:.1f} pts\033[0m\n{progress}\n"
        
        metrics += "═"*70 + "\n"
        
        # Active positions
        metrics += "🎯 Active Positions:\n"
        for symbol in self.symbols:
            if self.positions[symbol]:
                metrics += f"\n{symbol}:\n"
                for position in self.positions[symbol].values():
                    current_price = mt5.symbol_info_tick(symbol).ask if not self.simulate else position['entry_price']
                    metrics += self.format_trade_info(position, current_price, symbol)
        
        print(header + metrics)

    def update_terminal(self):
        """Clear terminal and update display"""
        os.system('cls' if os.name == 'nt' else 'clear')
        self.display_trade_metrics()

    def get_mt5_history(self, symbol, days=1):
        """Get trade history from MT5 for the specified symbol with enhanced error handling"""
        if self.simulate:
            return []
            
        try:
            from_date = datetime.now() - timedelta(days=days)
            to_date = datetime.now()
            
            # Get history deals
            deals = mt5.history_deals_get(from_date, to_date, symbol=symbol)
            if deals is None:
                self.logger.debug(f"No deals found for {symbol}")
                return []
                
            # Get history orders
            orders = mt5.history_orders_get(from_date, to_date, symbol=symbol)
            if orders is None:
                self.logger.debug(f"No orders found for {symbol}")
                return []
                
            # Create a mapping of order tickets to their details
            orders_dict = {order.ticket: order for order in orders}
            
            # Process deals into trade history
            trades = []
            for deal in deals:
                try:
                    order = orders_dict.get(deal.order)
                    if order:
                        # Safely get values with defaults
                        profit = getattr(deal, 'profit', 0.0)
                        commission = getattr(deal, 'commission', 0.0)
                        swap = getattr(deal, 'swap', 0.0)
                        
                        # Calculate points safely
                        profit_points = self.convert_to_points(profit, symbol)
                        
                        trade = {
                            "ticket": deal.order,
                            "type": "BUY" if deal.type == mt5.DEAL_TYPE_BUY else "SELL",
                            "profit": profit,
                            "profit_points": profit_points,
                            "timeframe": self.get_timeframe_name(order.type_time),
                            "entry_time": datetime.fromtimestamp(order.time_setup).strftime('%Y-%m-%d %H:%M:%S'),
                            "close_time": datetime.fromtimestamp(deal.time).strftime('%Y-%m-%d %H:%M:%S'),
                            "symbol": deal.symbol,
                            "status": "closed",
                            "lot_size": getattr(deal, 'volume', 0.01),  # Default to 0.01 if not available
                            "entry_price": getattr(order, 'price_open', 0.0),
                            "close_price": getattr(deal, 'price', 0.0),
                            "sl": getattr(order, 'sl', 0.0),
                            "tp": getattr(order, 'tp', 0.0),
                            "commission": commission,
                            "swap": swap,
                            "comment": getattr(deal, 'comment', '') or "MT5 Trade"
                        }
                        trades.append(trade)
                except Exception as e:
                    self.logger.debug(f"Error processing deal {deal.ticket}: {str(e)}")
                    continue
                
            return trades
            
        except Exception as e:
            self.logger.error(f"Error getting MT5 history: {str(e)}")
            return []

    def continuous_sync_loop(self):
        """Continuous synchronization loop with MT5."""
        while True:
            try:
                if not self.simulate:
                    current_time = datetime.now()
                    if (current_time - self.last_sync_time).total_seconds() >= self.sync_interval:
                        self.sync_with_mt5()
                        self.last_sync_time = current_time
                time.sleep(0.1)  # Small sleep to prevent CPU overuse
            except Exception as e:
                self.logger.error(f"Error in continuous sync loop: {str(e)}")
                time.sleep(1)

    def status_update_loop(self):
        """Run a background loop to update status bar."""
        while self.status_thread_running:
            try:
                self.update_status_line()
                time.sleep(self.status_update_interval)
            except Exception as e:
                self.logger.error(f"Error in status update loop: {str(e)}")
                time.sleep(5)  # Wait longer on error

    def sync_with_mt5(self):
        """Enhanced synchronization with MT5 including external trade management."""
        if self.simulate:
            return

        try:
            if not self.ensure_mt5_connection():
                return

            # Get all current MT5 positions
            mt5_positions = mt5.positions_get()
            if mt5_positions is None:
                self.logger.error(f"Failed to get positions from MT5: {mt5.last_error()}")
                return

            current_mt5_tickets = set()
            
            # Process current positions
            for pos in mt5_positions:
                symbol = pos.symbol
                ticket = pos.ticket
                current_mt5_tickets.add(ticket)
                
                if symbol in self.symbols:
                    # Check if this is a new position we're not tracking
                    if ticket not in self.positions[symbol]:
                        # This is an external trade - add it to our tracking
                        self.handle_external_trade(pos)
                    else:
                        # Update existing position details
                        self.update_position_details(pos)

            # Check for closed positions
            for symbol in self.symbols:
                for ticket in list(self.positions[symbol].keys()):
                    if ticket not in current_mt5_tickets:
                        self.handle_closed_position(symbol, ticket)

            # Sync history
            self.sync_trade_history()

        except Exception as e:
            self.logger.error(f"Error in sync_with_mt5: {str(e)}")

    def handle_external_trade(self, mt5_position):
        """Handle newly discovered external trade."""
        try:
            symbol = mt5_position.symbol
            ticket = mt5_position.ticket
            
            # Calculate default SL/TP if not set
            current_sl = mt5_position.sl
            current_tp = mt5_position.tp
            entry_price = mt5_position.price_open
            
            if current_sl == 0:  # No SL set
                sl_points = self.external_trade_defaults['sl_points']
                current_sl = entry_price - (sl_points * self.point[symbol]) if mt5_position.type == mt5.ORDER_TYPE_BUY else \
                            entry_price + (sl_points * self.point[symbol])
            
            if current_tp == 0:  # No TP set
                sl_distance = abs(entry_price - current_sl)
                current_tp = entry_price + (sl_distance * self.external_trade_defaults['tp_ratio']) if mt5_position.type == mt5.ORDER_TYPE_BUY else \
                            entry_price - (sl_distance * self.external_trade_defaults['tp_ratio'])
            
            # Create position object
            position = {
                'ticket': ticket,
                'type': mt5_position.type,
                'entry_price': entry_price,
                'lot_size': mt5_position.volume,
                'sl': current_sl,
                'tp': current_tp,
                'timeframe': self.external_trade_defaults['timeframe'],
                'strategy': 'external',
                'entry_time': datetime.fromtimestamp(mt5_position.time).strftime('%Y-%m-%d %H:%M:%S.%f'),
                'signal_time': datetime.fromtimestamp(mt5_position.time).strftime('%Y-%m-%d %H:%M:%S.%f'),
                'breakeven_triggered': False,
                'trailing_active': False,
                'thread_id': None,
                'reason': 'External trade',
                'comments': mt5_position.comment or 'External trade',
                'symbol': symbol,
                'profit': mt5_position.profit,
                'status': 'open'
            }
            
            # Add to our tracking
            with self.command_lock:
                self.positions[symbol][ticket] = position
                self.add_to_trade_history(position)
            
            # Modify SL/TP if needed
            if mt5_position.sl == 0 or mt5_position.tp == 0:
                self.modify_position(position, sl=current_sl, tp=current_tp)
            
            # Log and notify
            message = (
                f"📢 External Trade Detected and Added to Management:\n"
                f"Symbol: {symbol}\n"
                f"Ticket: {ticket}\n"
                f"Type: {'BUY' if mt5_position.type == mt5.ORDER_TYPE_BUY else 'SELL'}\n"
                f"Entry: {entry_price:.5f}\n"
                f"SL: {current_sl:.5f}\n"
                f"TP: {current_tp:.5f}\n"
                f"Volume: {mt5_position.volume:.2f}"
            )
            self.logger.info(message)
            self.send_telegram_message(message)

        except Exception as e:
            self.logger.error(f"Error handling external trade {mt5_position.ticket}: {str(e)}")

    def update_position_details(self, mt5_position):
        """Update tracked position with latest MT5 details."""
        try:
            symbol = mt5_position.symbol
            ticket = mt5_position.ticket
            position = self.positions[symbol][ticket]
            
            # Update core details
            position['profit'] = mt5_position.profit
            position['sl'] = mt5_position.sl
            position['tp'] = mt5_position.tp
            position['lot_size'] = mt5_position.volume
            
            # Check if SL/TP were removed externally
            if mt5_position.sl == 0 or mt5_position.tp == 0:
                self.logger.warning(f"SL/TP removed externally for ticket {ticket}, restoring...")
                self.modify_position(position, 
                                   sl=position['sl'] if mt5_position.sl == 0 else mt5_position.sl,
                                   tp=position['tp'] if mt5_position.tp == 0 else mt5_position.tp)
        
        except Exception as e:
            self.logger.error(f"Error updating position details for ticket {mt5_position.ticket}: {str(e)}")

    def handle_closed_position(self, symbol, ticket):
        """Handle position that was closed externally with enhanced error handling."""
        try:
            position = self.positions[symbol][ticket]
            
            # Get closing details from history
            history = mt5.history_deals_get(
                datetime.now() - timedelta(days=1),
                datetime.now(),
                ticket=ticket
            )
            
            try:
                if history and len(history) > 0:
                    closing_deal = history[-1]
                    # Safely get values with defaults
                    profit = getattr(closing_deal, 'profit', 0.0)
                    close_price = getattr(closing_deal, 'price', position.get('entry_price', 0.0))
                    close_time = datetime.fromtimestamp(getattr(closing_deal, 'time', datetime.now().timestamp()))
                else:
                    # If no history found, use last known position details
                    profit = position.get('profit', 0.0)
                    close_price = position.get('entry_price', 0.0)
                    close_time = datetime.now()
                
                # Calculate points safely
                try:
                    point_value = self.point.get(symbol, 0.0)
                    lot_size = position.get('lot_size', self.lot_size)
                    profit_points = (profit / (point_value * lot_size * 10000)) if all(v is not None and v != 0 for v in [profit, point_value, lot_size]) else 0.0
                except Exception as e:
                    self.logger.debug(f"Error calculating profit points: {str(e)}")
                    profit_points = 0.0
                
                # Update trade history
                self.update_trade_history_on_close(
                    ticket, symbol, profit_points, 
                    f"Closed externally at {close_price:.5f}"
                )
                
                # Remove from tracking
                with self.command_lock:
                    if ticket in self.positions[symbol]:
                        del self.positions[symbol][ticket]
                
                # Log and notify
                message = (
                    f"📢 Position Closed Externally:\n"
                    f"Symbol: {symbol}\n"
                    f"Ticket: {ticket}\n"
                    f"Profit: {profit_points:.2f} points\n"
                    f"Close Time: {close_time}"
                )
                self.logger.info(message)
                self.send_telegram_message(message)
                
            except Exception as e:
                self.logger.error(f"Error processing closing details for ticket {ticket}: {str(e)}")
                # Still try to remove the position from tracking
                with self.command_lock:
                    if ticket in self.positions[symbol]:
                        del self.positions[symbol][ticket]
        
        except Exception as e:
            self.logger.error(f"Error handling closed position {ticket}: {str(e)}")

    def sync_trade_history(self):
        """Synchronize trade history with MT5."""
        try:
            for symbol in self.symbols:
                try:
                    # Get today's history
                    history = self.get_mt5_history(symbol, days=1)
                    if not history:  # Skip if no history
                        continue
                
                    # Process new history entries
                    current_tickets = set(trade['ticket'] for trade in history)
                    new_tickets = current_tickets - self.last_known_history[symbol]
                
                    for trade in history:
                        if trade['ticket'] in new_tickets:
                            try:
                                # Add to appropriate history list based on comment/type
                                if 'grid' in trade['comment'].lower():
                                    self.grid_history[symbol].append(trade)
                                elif 'suretrend' in trade['comment'].lower():
                                    self.suretrend_history[symbol].append(trade)
                                elif 'momentum' in trade['comment'].lower():
                                    self.momentum_history[symbol].append(trade)
                                else:
                                    self.trade_history[symbol].append(trade)
                            except Exception as e:
                                self.logger.error(f"Error processing trade {trade['ticket']}: {str(e)}")
                                continue
                
                    # Update known history
                    self.last_known_history[symbol] = current_tickets
                
                    # Save updated history
                    self.save_trade_history()
                
                except Exception as e:
                    self.logger.error(f"Error syncing history for {symbol}: {str(e)}")
                    continue
    
        except Exception as e:
            self.logger.error(f"Error in sync_trade_history: {str(e)}")

    def fetch_chart(self, symbol, timeframe):
        """Generate and display a chart for the specified symbol and timeframe."""
        try:
            # Convert timeframe string to MT5 timeframe if needed
            if isinstance(timeframe, str):
                timeframe = self.timeframe_configs.get(timeframe.upper())
                if timeframe is None:
                    return f"Invalid timeframe. Available timeframes: {', '.join(self.timeframe_configs.keys())}"

            # Get latest data
            df = self.get_or_update_rates(symbol, timeframe)
            if df is None:
                return f"Failed to get data for {symbol} on {self.get_timeframe_name(timeframe)}"

            # Calculate indicators
            df = self.calculate_indicators(df, timeframe, symbol)
            if df is None:
                return f"Failed to calculate indicators for {symbol} on {self.get_timeframe_name(timeframe)}"

            # Create figure
            fig = go.Figure()

            # Add candlestick chart
            fig.add_trace(go.Candlestick(
                x=df['time'],
                open=df['open'],
                high=df['high'],
                low=df['low'],
                close=df['close'],
                name='OHLC'
            ))

            # Add moving averages
            fig.add_trace(go.Scatter(
                x=df['time'],
                y=df['ma_fast'],
                mode='lines',
                name=f'Fast MA ({self.ma_configs[timeframe]["fast"]})',
                line=dict(color='blue')
            ))
            fig.add_trace(go.Scatter(
                x=df['time'],
                y=df['ma_slow'],
                mode='lines',
                name=f'Slow MA ({self.ma_configs[timeframe]["slow"]})',
                line=dict(color='red')
            ))

            # Add PSAR
            fig.add_trace(go.Scatter(
                x=df['time'],
                y=df['psar'],
                mode='markers',
                name='PSAR',
                marker=dict(
                    color='purple',
                    size=4,
                    symbol='diamond'
                )
            ))

            # Add Bollinger Bands
            fig.add_trace(go.Scatter(
                x=df['time'],
                y=df['bb_upper'],
                mode='lines',
                name='BB Upper',
                line=dict(color='gray', dash='dash')
            ))
            fig.add_trace(go.Scatter(
                x=df['time'],
                y=df['bb_lower'],
                mode='lines',
                name='BB Lower',
                line=dict(color='gray', dash='dash'),
                fill='tonexty'
            ))

            # Add open positions if any
            if symbol in self.positions:
                for ticket, pos in self.positions[symbol].items():
                    if pos['timeframe'] == timeframe:
                        # Add entry line
                        fig.add_hline(
                            y=pos['entry_price'],
                            line_dash="dash",
                            line_color="green" if pos['type'] == mt5.ORDER_TYPE_BUY else "red",
                            annotation_text=f"Entry {ticket}"
                        )
                        # Add SL line
                        if pos['sl'] > 0:
                            fig.add_hline(
                                y=pos['sl'],
                                line_dash="dot",
                                line_color="red",
                                annotation_text=f"SL {ticket}"
                            )
                        # Add TP line
                        if pos['tp'] > 0:
                            fig.add_hline(
                                y=pos['tp'],
                                line_dash="dot",
                                line_color="green",
                                annotation_text=f"TP {ticket}"
                            )

            # Update layout
            fig.update_layout(
                title=f'{symbol} {self.get_timeframe_name(timeframe)} Chart',
                yaxis_title='Price',
                xaxis_title='Time',
                template='plotly_dark'
            )

            # Save chart
            filename = f"chart_{symbol}_{self.get_timeframe_name(timeframe)}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.html"
            fig.write_html(filename)

            # Send to Telegram if configured
            if self.TELEGRAM_BOT_TOKEN and self.TELEGRAM_CHAT_ID:
                # Save as image for Telegram
                img_filename = f"chart_{symbol}_{self.get_timeframe_name(timeframe)}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.png"
                fig.write_image(img_filename)
                self.send_telegram_message(
                    f"Chart for {symbol} {self.get_timeframe_name(timeframe)}",
                    chart_path=img_filename
                )

            return f"Chart saved as {filename}"

        except Exception as e:
            self.logger.error(f"Error generating chart: {str(e)}")
            return f"Failed to generate chart: {str(e)}"

    def check_hfscalper_signal(self, df, timeframe, symbol):
        """Check for HFScalper strategy signals on M1 timeframe."""
        if len(df) < 10:
            return None, "Insufficient data", None
            
        try:
            # Get the last few candles for analysis
            window = df.iloc[-5:].copy()  # Use last 5 candles for quick analysis
            latest = window.iloc[-1]
            prev = window.iloc[-2]
            signal_time = datetime.now()
            
            # 1. Check MA trend
            ma_trend_up = latest['ma_fast'] > latest['ma_slow']
            ma_trend_down = latest['ma_fast'] < latest['ma_slow']
            
            # 2. Check momentum
            momentum_increasing = latest['momentum'] > prev['momentum']
            momentum_strong = abs(latest['momentum']) > self.hfscalper_min_momentum
            
            # 3. Check volatility
            current_atr = latest['atr']
            avg_atr = df['atr'].tail(20).mean()
            volatility_ok = current_atr <= (avg_atr * self.hfscalper_volatility_threshold)
            
            # 4. Price action confirmation
            price_action_up = latest['close'] > latest['open'] and latest['close'] > prev['close']
            price_action_down = latest['close'] < latest['open'] and latest['close'] < prev['close']
            
            # 5. Check PSAR if enabled
            psar_ok = True
            if self.hfscalper_psar_enabled:
                psar_bullish = latest['close'] > latest['psar']
                psar_bearish = latest['close'] < latest['psar']
                psar_ok = (psar_bullish and price_action_up) or (psar_bearish and price_action_down)
            
            # Buy conditions
            buy_conditions = (
                ma_trend_up and
                momentum_increasing and
                momentum_strong and
                volatility_ok and
                price_action_up and
                latest['macd'] > latest['macd_signal'] and
                latest['close'] > latest['bb_middle'] and
                psar_ok
            )
            
            # Sell conditions
            sell_conditions = (
                ma_trend_down and
                momentum_increasing and
                momentum_strong and
                volatility_ok and
                price_action_down and
                latest['macd'] < latest['macd_signal'] and
                latest['close'] < latest['bb_middle'] and
                psar_ok
            )
            
            if buy_conditions:
                return "BUY", "HFScalper BUY signal", signal_time
            elif sell_conditions:
                return "SELL", "HFScalper SELL signal", signal_time
            return None, "No HFScalper signal", None
            
        except Exception as e:
            self.logger.error(f"Error checking HFScalper signal for {symbol}: {str(e)}")
            return None, f"Error checking HFScalper signal: {str(e)}", None

    def handle_hfscalper_trade(self, symbol, df):
        """Handle HFScalper trade management with tight stops and quick profits."""
        try:
            positions = [p for p in self.positions[symbol].values() if p['strategy'] == 'hfscalper']
            current_price = df['close'].iloc[-1]
            
            for position in positions:
                # Calculate profit in points
                profit_points = self.convert_to_points(
                    current_price - position['entry_price'] if position['type'] == mt5.ORDER_TYPE_BUY 
                    else position['entry_price'] - current_price, 
                    symbol
                )
                
                # Quick exit on target reached
                if profit_points >= self.hfscalper_tp_points:
                    self.close_position(position, f"HFScalper TP reached: {profit_points:.1f} points")
                    continue
                
                # Tight trailing stop
                if profit_points >= self.hfscalper_tp_points * 0.5:  # Activate trailing at 50% of target
                    trail_points = self.hfscalper_tp_points * 0.2  # 20% of target as trailing distance
                    if position['type'] == mt5.ORDER_TYPE_BUY:
                        new_sl = current_price - (trail_points * self.point[symbol])
                        if new_sl > position['sl']:
                            self.modify_position(position, sl=new_sl)
                    else:
                        new_sl = current_price + (trail_points * self.point[symbol])
                        if new_sl < position['sl']:
                            self.modify_position(position, sl=new_sl)
                
                # Check for reversal signals
                if self.check_hfscalper_reversal(position, df):
                    self.close_position(position, "HFScalper reversal signal")
                    
        except Exception as e:
            self.logger.error(f"Error in handle_hfscalper_trade: {str(e)}")

    def check_hfscalper_reversal(self, position, df):
        """Check for HFScalper strategy reversal signals."""
        try:
            latest = df.iloc[-1]
            prev = df.iloc[-2]
            
            # For long positions
            if position['type'] == mt5.ORDER_TYPE_BUY:
                return (
                    latest['ma_fast'] < latest['ma_slow'] and
                    latest['momentum'] < 0 and
                    latest['close'] < latest['bb_middle'] and
                    (not self.hfscalper_psar_enabled or latest['close'] < latest['psar'])
                )
            # For short positions
            else:
                return (
                    latest['ma_fast'] > latest['ma_slow'] and
                    latest['momentum'] > 0 and
                    latest['close'] > latest['bb_middle'] and
                    (not self.hfscalper_psar_enabled or latest['close'] > latest['psar'])
                )
                
        except Exception as e:
            self.logger.error(f"Error in check_hfscalper_reversal: {str(e)}")
            return False

    def optimize_signals(self):
        """Enable signal optimization with enhanced filtering and quality checks."""
        self.signal_optimization_enabled = True
        self.logger.info("Signal optimization enabled with enhanced filtering")
        return "Signal optimization enabled with enhanced filtering and quality checks"

    def disable_signal_optimization(self):
        """Disable signal optimization."""
        self.signal_optimization_enabled = False
        self.logger.info("Signal optimization disabled")
        return "Signal optimization disabled"

    def set_signal_interval(self, interval):
        """Set the interval for signal checking in seconds."""
        try:
            interval = float(interval)
            if interval < 0.1:
                return "Signal interval must be at least 0.1 seconds"
            self.signal_interval = interval
            return f"Signal checking interval set to {interval} seconds"
        except ValueError:
            return "Invalid interval value"

    def handle_breakout_momentum_trade(self, symbol, df):
        """Handle Breakout Momentum trade management."""
        try:
            positions = [p for p in self.positions[symbol].values() if p['strategy'] == 'breakout_momentum']
            current_price = df['close'].iloc[-1]
            
            for position in positions:
                # Calculate profit in points
                profit_points = self.convert_to_points(
                    current_price - position['entry_price'] if position['type'] == mt5.ORDER_TYPE_BUY 
                    else position['entry_price'] - current_price, 
                    symbol
                )
                
                # Dynamic trailing stop based on ATR
                atr = df['atr'].iloc[-1]
                if profit_points >= position['break_even']:
                    if not position['breakeven_triggered']:
                        self.modify_position(position, sl=position['entry_price'])
                        position['breakeven_triggered'] = True
                    
                    if not position['trailing_active'] and profit_points >= position['trailing_stop_delay']:
                        trail_distance = atr * self.atr_multiplier_trailing
                        if position['type'] == mt5.ORDER_TYPE_BUY:
                            new_sl = current_price - trail_distance
                            if new_sl > position['sl']:
                                self.modify_position(position, sl=new_sl)
                                position['trailing_active'] = True
                        else:
                            new_sl = current_price + trail_distance
                            if new_sl < position['sl']:
                                self.modify_position(position, sl=new_sl)
                                position['trailing_active'] = True
                
                # Check for consolidation reversal
                if self.check_breakout_reversal(position, df):
                    self.close_position(position, "Breakout Momentum reversal signal")
                    
        except Exception as e:
            self.logger.error(f"Error in handle_breakout_momentum_trade: {str(e)}")

    def check_breakout_reversal(self, position, df):
        """Check for Breakout Momentum strategy reversal signals."""
        try:
            latest = df.iloc[-1]
            window = df.iloc[-self.consolidation_lookback:]
            
            # Calculate consolidation
            bb_width = (latest['bb_upper'] - latest['bb_lower']) / latest['bb_middle']
            price_range = window['high'].max() - window['low'].min()
            avg_range = price_range / len(window)
            
            # New consolidation forming
            consolidation_forming = bb_width < self.consolidation_threshold
            
            # For long positions
            if position['type'] == mt5.ORDER_TYPE_BUY:
                return (
                    consolidation_forming and
                    latest['close'] < latest['ma_slow'] and
                    latest['macd'] < latest['macd_signal'] and
                    latest['rsi'] > self.rsi_overbought and
                    latest['close'] < latest['psar']
                )
            # For short positions
            else:
                return (
                    consolidation_forming and
                    latest['close'] > latest['ma_slow'] and
                    latest['macd'] > latest['macd_signal'] and
                    latest['rsi'] < self.rsi_oversold and
                    latest['close'] > latest['psar']
                )
                
        except Exception as e:
            self.logger.error(f"Error in check_breakout_reversal: {str(e)}")
            return False

    def get_signal_stats(self, symbol=None, timeframe=None):
        """Get detailed signal statistics for specified symbol and timeframe."""
        stats = []
        symbols = [symbol] if symbol else self.symbols
        timeframes = [timeframe] if timeframe else self.timeframes
        
        for sym in symbols:
            for tf in timeframes:
                if sym in self.signal_performance and tf in self.signal_performance[sym]:
                    perf = self.signal_performance[sym][tf]
                    total = perf['total']
                    successful = perf['successful']
                    accuracy = (successful / total * 100) if total > 0 else 0
                    stats.append(f"{sym} {self.get_timeframe_name(tf)}:")
                    stats.append(f"  Total Signals: {total}")
                    stats.append(f"  Successful: {successful}")
                    stats.append(f"  Accuracy: {accuracy:.2f}%")
        
        return "\n".join(stats) if stats else "No signal statistics available"

    def evaluate_signal_quality(self, symbol, timeframe, signal_type):
        """Evaluate the quality of a signal based on multiple factors."""
        try:
            df = self.get_or_update_rates(symbol, timeframe)
            if df is None or len(df) < 20:
                return 0.0

            quality_score = 0.0
            weights = {
                'trend_strength': 0.3,
                'momentum': 0.2,
                'volatility': 0.2,
                'confirmation': 0.3
            }

            # Trend strength
            ma_fast = df['ma_fast'].iloc[-1]
            ma_slow = df['ma_slow'].iloc[-1]
            trend_strength = abs(ma_fast - ma_slow) / ma_slow
            quality_score += weights['trend_strength'] * min(trend_strength * 100, 1.0)

            # Momentum
            momentum = abs(df['momentum'].iloc[-1])
            avg_momentum = abs(df['momentum'].rolling(window=20).mean().iloc[-1])
            momentum_score = min(momentum / avg_momentum, 1.0) if avg_momentum > 0 else 0
            quality_score += weights['momentum'] * momentum_score

            # Volatility
            current_atr = df['atr'].iloc[-1]
            avg_atr = df['atr'].rolling(window=20).mean().iloc[-1]
            volatility_score = 1.0 - min(current_atr / avg_atr, 1.0) if avg_atr > 0 else 0
            quality_score += weights['volatility'] * volatility_score

            # Confirmation signals
            confirmations = 0
            if df['macd_crossover'].iloc[-1] or df['macd_crossunder'].iloc[-1]:
                confirmations += 1
            if df['bb_expanding'].iloc[-1]:
                confirmations += 1
            if (signal_type == "BUY" and df['close'].iloc[-1] > df['psar'].iloc[-1]) or \
               (signal_type == "SELL" and df['close'].iloc[-1] < df['psar'].iloc[-1]):
                confirmations += 1
            
            confirmation_score = min(confirmations / 3, 1.0)
            quality_score += weights['confirmation'] * confirmation_score

            return quality_score

        except Exception as e:
            self.logger.error(f"Error evaluating signal quality: {str(e)}")
            return 0.0

    def check_signal_filters(self, df, symbol, timeframe):
        """Check if signal passes all filters."""
        try:
            if not df or len(df) < 20:
                return False

            # Check momentum
            current_momentum = abs(df['momentum'].iloc[-1])
            if current_momentum < self.signal_filters['momentum_threshold']:
                return False

            # Check volatility
            current_atr = df['atr'].iloc[-1]
            avg_atr = df['atr'].rolling(window=20).mean().iloc[-1]
            if avg_atr > 0 and current_atr / avg_atr > self.signal_filters['volatility_threshold']:
                return False

            # Check minimum confirmations
            confirmations = 0
            if df['macd_crossover'].iloc[-1] or df['macd_crossunder'].iloc[-1]:
                confirmations += 1
            if df['bb_expanding'].iloc[-1]:
                confirmations += 1
            if abs(df['momentum'].iloc[-1]) > abs(df['momentum'].iloc[-2]):
                confirmations += 1
            
            if confirmations < self.signal_filters['min_confirmation_signals']:
                return False

            return True

        except Exception as e:
            self.logger.error(f"Error checking signal filters: {str(e)}")
            return False

    def update_signal_history(self, symbol, timeframe, signal_type, quality):
        """Update signal history with new signal."""
        try:
            signal = {
                'timestamp': datetime.now(),
                'type': signal_type,
                'quality': quality,
                'price': self.get_current_price(symbol)
            }
            self.signal_history[symbol][timeframe].append(signal)
            
            # Keep only last 1000 signals
            if len(self.signal_history[symbol][timeframe]) > 1000:
                self.signal_history[symbol][timeframe] = self.signal_history[symbol][timeframe][-1000:]
                
        except Exception as e:
            self.logger.error(f"Error updating signal history: {str(e)}")

    def get_current_price(self, symbol):
        """Get current market price for symbol."""
        if self.simulate:
            return 0.0
        try:
            tick = mt5.symbol_info_tick(symbol)
            if tick:
                return (tick.bid + tick.ask) / 2
            return 0.0
        except Exception as e:
            self.logger.error(f"Error getting current price: {str(e)}")
            return 0.0

    def process_realtime_signal(self, symbol, timeframe, signal_type, message, signal_time):
        """Process a real-time signal with optimization and filtering."""
        try:
            if not self.realtime_signals_enabled:
                return None, "Real-time signals disabled"

            # Get latest data
            df = self.get_or_update_rates(symbol, timeframe)
            if df is None:
                return None, "Failed to get market data"

            # Check filters
            if self.signal_optimization_enabled and not self.check_signal_filters(df, symbol, timeframe):
                return None, "Signal did not pass filters"

            # Evaluate signal quality
            quality = self.evaluate_signal_quality(symbol, timeframe, signal_type)
            if quality < self.signal_quality_threshold:
                return None, f"Signal quality {quality:.2f} below threshold {self.signal_quality_threshold}"

            # Update signal history
            self.update_signal_history(symbol, timeframe, signal_type, quality)

            # Create enhanced signal message
            enhanced_message = (
                f"🎯 High Quality Signal Detected 🎯\n"
                f"Strategy: {message}\n"
                f"Signal Quality: {quality:.2f}\n"
                f"Current Price: {self.get_current_price(symbol):.5f}\n"
                f"Timeframe: {self.get_timeframe_name(timeframe)}"
            )

            # Log signal if enabled
            if self.signal_logging_enabled:
                self.logger.info(f"[{symbol}] {enhanced_message}")

            # Send alert if enabled
            if self.signal_alerts_enabled:
                self.send_telegram_message(enhanced_message)

            return signal_type, enhanced_message

        except Exception as e:
            self.logger.error(f"Error processing real-time signal: {str(e)}")
            return None, f"Error processing signal: {str(e)}"

class MockTradeManager:
    def __init__(self, trading_strategy):
        self.trading_strategy = trading_strategy
        self.mock_trades = {}  # Format: {ticket: trade_info}
        self.next_ticket = 1000
        self.lock = threading.Lock()
        self.active_threads = {}  # Format: {ticket: thread}
        
    def generate_ticket(self):
        """Generate unique ticket number for mock trades."""
        with self.lock:
            ticket = self.next_ticket
            self.next_ticket += 1
            return ticket
    
    def create_mock_trade(self, symbol, trade_type, timeframe, lot_size=0.01):
        """Create a new mock trade with enhanced error handling."""
        try:
            if symbol not in self.trading_strategy.symbols:
                return None, f"Invalid symbol: {symbol}"
            if trade_type not in ["BUY", "SELL"]:
                return None, f"Invalid trade type: {trade_type}"
            if lot_size <= 0:
                return None, "Lot size must be positive"
            
            # Get current market data
            df = self.trading_strategy.get_or_update_rates(symbol, timeframe)
            if df is None or len(df) < 1:
                return None, "Failed to get market data"
            
            current_price = df['close'].iloc[-1]
            entry_time = datetime.now()
            ticket = self.generate_ticket()
            
            trade_info = {
                'ticket': ticket,
                'symbol': symbol,
                'type': trade_type,
                'entry_price': current_price,
                'current_price': current_price,
                'lot_size': lot_size,
                'entry_time': entry_time,
                'timeframe': timeframe,
                'profit_points': 0,
                'status': 'open',
                'close_price': None,
                'close_time': None,
                'close_reason': None
            }
            
            # Start background monitoring thread
            thread = threading.Thread(
                target=self.monitor_mock_trade,
                args=(ticket, trade_info),
                daemon=True
            )
            
            with self.lock:
                self.mock_trades[ticket] = trade_info
                self.active_threads[ticket] = thread
            
            thread.start()
            
            return ticket, f"Mock trade #{ticket} created for {symbol} ({trade_type})"
            
        except Exception as e:
            return None, f"Error creating mock trade: {str(e)}"
    
    def monitor_mock_trade(self, ticket, trade_info):
        """Monitor mock trade in background with enhanced exit conditions."""
        try:
            max_duration = timedelta(minutes=30)  # Close after 30 minutes
            stop_loss_points = 50  # 50 points stop-loss
            start_time = trade_info['entry_time']
            
            while True:
                if ticket not in self.mock_trades:
                    break
                
                # Check duration
                if datetime.now() - start_time > max_duration:
                    self.close_mock_trade(ticket, "Time-based exit", trade_info['current_price'])
                    break
                
                # Get latest data
                df = self.trading_strategy.get_or_update_rates(trade_info['symbol'], trade_info['timeframe'])
                if df is None:
                    time.sleep(1)
                    continue
                
                current_price = df['close'].iloc[-1]
                
                # Update trade info
                with self.lock:
                    if ticket in self.mock_trades:
                        trade_info['current_price'] = current_price
                        
                        # Calculate profit in points
                        point = self.trading_strategy.point[trade_info['symbol']]
                        profit_points = (current_price - trade_info['entry_price']) / point
                        if trade_info['type'] == "SELL":
                            profit_points = -profit_points
                        trade_info['profit_points'] = profit_points
                        
                        # Check stop-loss
                        if abs(profit_points) >= stop_loss_points and profit_points < 0:
                            self.close_mock_trade(ticket, f"Stop-loss triggered at {profit_points:.1f} points", current_price)
                            break
                        
                        # Check MA crossover exit
                        if self.check_ma_exit(df, trade_info):
                            self.close_mock_trade(ticket, "MA Crossover Exit", current_price)
                            break
                
                time.sleep(1)
                
        except Exception as e:
            self.trading_strategy.logger.error(f"Error monitoring mock trade #{ticket}: {str(e)}")
    
    def check_ma_exit(self, df, trade_info):
        """Check for MA crossover exit signal."""
        if len(df) < 2:
            return False
            
        latest = df.iloc[-1]
        prev = df.iloc[-2]
        
        if trade_info['type'] == "BUY":
            return (latest['ma_fast'] < latest['ma_slow'] and 
                   prev['ma_fast'] >= prev['ma_slow'])
        else:
            return (latest['ma_fast'] > latest['ma_slow'] and 
                   prev['ma_fast'] <= prev['ma_slow'])
    
    def close_mock_trade(self, ticket, reason="Manual close", close_price=None):
        """Close a mock trade."""
        with self.lock:
            if ticket not in self.mock_trades:
                return False, "Trade not found"
            
            trade = self.mock_trades[ticket]
            trade['status'] = 'closed'
            trade['close_time'] = datetime.now()
            trade['close_price'] = close_price or trade['current_price']
            trade['close_reason'] = reason
            
            # Clean up
            if ticket in self.active_threads:
                del self.active_threads[ticket]
            del self.mock_trades[ticket]
            
            return True, f"Mock trade #{ticket} closed: {reason}"
    
    def get_mock_trade_info(self, ticket=None):
        """Get information about mock trades."""
        with self.lock:
            if ticket is not None:
                if ticket not in self.mock_trades:
                    return f"Mock trade #{ticket} not found"
                return self.format_mock_trade_info(self.mock_trades[ticket])
            
            if not self.mock_trades:
                return "No active mock trades"
            
            return "\n\n".join([self.format_mock_trade_info(trade) 
                               for trade in self.mock_trades.values()])
    
    def format_mock_trade_info(self, trade):
        """Format mock trade information for display."""
        duration = datetime.now() - trade['entry_time']
        stop_loss = trade['entry_price'] - (50 * self.trading_strategy.point[trade['symbol']]) if trade['type'] == "BUY" else \
                    trade['entry_price'] + (50 * self.trading_strategy.point[trade['symbol']])
        
        return (
            f"🎯 Mock Trade #{trade['ticket']}\n"
            f"Symbol: {trade['symbol']}\n"
            f"Type: {trade['type']}\n"
            f"Timeframe: {self.trading_strategy.get_timeframe_name(trade['timeframe'])}\n"
            f"Entry: {trade['entry_price']:.5f}\n"
            f"Current: {trade['current_price']:.5f}\n"
            f"Stop-Loss: {stop_loss:.5f}\n"
            f"Profit: {trade['profit_points']:.1f} points\n"
            f"Duration: {str(duration).split('.')[0]}\n"
            f"Status: {trade['status']}"
        )

class TerminalManager:
    def __init__(self):
        self.terminal_width = shutil.get_terminal_size().columns
        self.current_status = ""
        self.last_update = datetime.now()
        self.status_refresh_rate = 1  # seconds
        
        # ANSI color codes
        self.COLORS = {
            'reset': '\033[0m',
            'bold': '\033[1m',
            'dim': '\033[2m',
            'red': '\033[31m',
            'green': '\033[32m',
            'yellow': '\033[33m',
            'blue': '\033[34m',
            'magenta': '\033[35m',
            'cyan': '\033[36m',
            'white': '\033[37m',
            'bg_black': '\033[40m',
            'bg_red': '\033[41m',
            'bg_green': '\033[42m'
        }
        
        # Unicode symbols
        self.SYMBOLS = {
            'arrow': '→',
            'bullet': '•',
            'check': '✓',
            'cross': '✗',
            'warning': '⚠',
            'info': 'ℹ',
            'profit': '↑',
            'loss': '↓',
            'signal': '🎯',
            'chart': '📊',
            'money': '💰'
        }
        
    def clear_screen(self):
        """Clear the terminal screen."""
        os.system('cls' if os.name == 'nt' else 'clear')
        
    def create_header(self, text, style='double'):
        """Create a pretty header."""
        width = self.terminal_width
        if style == 'double':
            return f"\n{'═' * width}\n{text.center(width)}\n{'═' * width}\n"
        return f"\n{'─' * width}\n{text.center(width)}\n{'─' * width}\n"
    
    def format_section(self, title, content):
        """Format a section with title and content."""
        width = self.terminal_width
        return (
            f"{self.COLORS['bold']}{self.SYMBOLS['bullet']} {title}{self.COLORS['reset']}\n"
            f"{content}\n{'─' * width}\n"
        )
    
    def format_message(self, msg_type, message):
        """Format different types of messages."""
        prefix = {
            'error': f"{self.COLORS['red']}{self.SYMBOLS['cross']}",
            'success': f"{self.COLORS['green']}{self.SYMBOLS['check']}",
            'warning': f"{self.COLORS['yellow']}{self.SYMBOLS['warning']}",
            'info': f"{self.COLORS['blue']}{self.SYMBOLS['info']}",
            'signal': f"{self.COLORS['magenta']}{self.SYMBOLS['signal']}",
            'profit': f"{self.COLORS['green']}{self.SYMBOLS['profit']}",
            'loss': f"{self.COLORS['red']}{self.SYMBOLS['loss']}"
        }.get(msg_type, f"{self.COLORS['white']}{self.SYMBOLS['bullet']}")
        
        return f"{prefix} {message}{self.COLORS['reset']}"
    
    def create_progress_bar(self, value, total, width=40):
        """Create a colorful progress bar."""
        percentage = value / total
        filled = int(width * percentage)
        bar = (
            f"{self.COLORS['green']}{'█' * filled}"
            f"{self.COLORS['dim']}{'░' * (width - filled)}{self.COLORS['reset']}"
        )
        return f"[{bar}] {percentage:.1%}"
    
    def format_trade_status(self, position):
        """Format trade position status."""
        profit_color = self.COLORS['green'] if position['profit'] >= 0 else self.COLORS['red']
        return (
            f"{self.COLORS['bold']}{position['symbol']} #{position['ticket']}{self.COLORS['reset']} "
            f"({position['type']}) @ {position['entry_price']:.5f}\n"
            f"Profit: {profit_color}{position['profit']:.2f}{self.COLORS['reset']} pts"
        )
    
    def update_status(self, status):
        """Update the status line at the bottom of the terminal."""
        try:
            if (datetime.now() - self.last_update).total_seconds() >= self.status_refresh_rate:
                sys.stdout.write(f"\033[s")  # Save cursor position
                sys.stdout.write(f"\033[0J")  # Clear from cursor to end of screen
                sys.stdout.write(f"\033[{self.terminal_width}D")  # Move to start of line
                sys.stdout.write(f"\033[K")  # Clear line
                sys.stdout.write(f"{self.COLORS['dim']}{status}{self.COLORS['reset']}")
                sys.stdout.write(f"\033[u")  # Restore cursor position
                sys.stdout.flush()
                self.last_update = datetime.now()
        except Exception as e:
            print(f"Error updating status: {str(e)}")
def main():
    parser = argparse.ArgumentParser(description="Trading Strategy Script")
    parser.add_argument("--symbols", nargs="+", default=["XAUUSD"], help="List of trading symbols")
    parser.add_argument("--timeframes", nargs="+", default=["M1"], help="List of timeframes")
    parser.add_argument("--lot-size", type=float, default=0.01, help="Lot size for trades")
    parser.add_argument("--daily-max-profit", type=float, default=1000.0, help="Daily maximum profit limit in points")
    parser.add_argument("--simulate", action="store_true", help="Run in simulation mode")
    parser.add_argument("--risk-percent", type=float, default=2.0, help="Risk percentage per trade")
    parser.add_argument("--mt5-login", type=int, help="MT5 account login")
    parser.add_argument("--mt5-password", type=str, help="MT5 account password")
    parser.add_argument("--mt5-server", type=str, help="MT5 server name")
    args = parser.parse_args()

    dummy_strategy = TradingStrategy()
    for tf in args.timeframes:
        if tf not in dummy_strategy.timeframe_configs:
            print(f"Error: Invalid timeframe '{tf}'. Available timeframes: {', '.join(dummy_strategy.timeframe_configs.keys())}")
            sys.exit(1)

    strategy = TradingStrategy(
        mt5_path=r"C:\Program Files\Pepperstone MetaTrader 5\terminal64.exe",
        symbols=args.symbols,
        timeframes=args.timeframes,
        lot_size=args.lot_size,
        daily_max_profit=args.daily_max_profit,
        simulate=args.simulate,
        risk_percent=args.risk_percent,
        mt5_login=args.mt5_login,
        mt5_password=args.mt5_password,
        mt5_server=args.mt5_server
    )
    strategy.run()

if __name__ == "__main__":
    main()