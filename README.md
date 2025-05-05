# <img src="https://github.com/benzmuircroft/temp/blob/main/Yjs.png" height="32" style="vertical-align:40px;"/>🍐@ypear/currency 🧮

### 💾 Installation
```bash
npm install @ypear/currency
```

## 👀 Description
A JavaScript utility for performing precise mathematical operations on large numbers represented as strings, with comprehensive support for cryptocurrency-style decimal conversions (8/16 decimal places).

### ✅ Usage
```javascript
const cc = require('@ypear/currency');

// Basic arithmetic
cc.add('4', '710000000000000000'); // String addition
cc.sub('5', '3'); // String subtraction

// Decimal conversions
cc.qsat_to_coin('10000000000000000'); // Convert qsats to coins (16→8 decimal places)
cc.qsat_to_qoin('10000000000000000'); // Convert qsats to qoins (16 decimal format)
cc.sat_to_coin('100000000'); // Convert sats to coins (8 decimal format)
cc.coin_to_qsat('1.00000000'); // Convert coins to qsats

// Formatted display
cc.qsat_to_readable('10000000000000000'); // Returns formatted string with subscript digits
cc.fixed('1.23456789', 4); // Returns '1.2345'
```

### 🧰 Example Methods
- `calc_share(my_balance, total, new_reward)` - Calculate proportional share
- `pct_to_share(percent, of_number)` - Convert percentage to share
- `share_to_pct(balance, total)` - Convert share to percentage
- `no_e(x)` - Convert scientific notation to fixed string


### 📜 License
MIT
