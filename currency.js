//https://github.com/peterolson/BigInteger.js
var bigInt = function(undefined) {
  "use strict";
  var BASE = 1e7,
      LOG_BASE = 7,
      MAX_INT = 9007199254740992,
      MAX_INT_ARR = smallToArray(MAX_INT),
      DEFAULT_ALPHABET = "0123456789abcdefghijklmnopqrstuvwxyz";
  var supportsNativeBigInt = typeof BigInt === "function";

  function Integer(v, radix, alphabet, caseSensitive) {
      if (typeof v === "undefined") return Integer[0];
      if (typeof radix !== "undefined") return +radix === 10 && !alphabet ? parseValue(v) : parseBase(v, radix, alphabet, caseSensitive);
      return parseValue(v)
  }

  function BigInteger(value, sign) {
      this.value = value;
      this.sign = sign;
      this.isSmall = false
  }
  BigInteger.prototype = Object.create(Integer.prototype);

  function SmallInteger(value) {
      this.value = value;
      this.sign = value < 0;
      this.isSmall = true
  }
  SmallInteger.prototype = Object.create(Integer.prototype);

  function NativeBigInt(value) {
      this.value = value
  }
  NativeBigInt.prototype = Object.create(Integer.prototype);

  function isPrecise(n) {
      return -MAX_INT < n && n < MAX_INT
  }

  function smallToArray(n) {
      if (n < 1e7) return [n];
      if (n < 1e14) return [n % 1e7, Math.floor(n / 1e7)];
      return [n % 1e7, Math.floor(n / 1e7) % 1e7, Math.floor(n / 1e14)]
  }

  function arrayToSmall(arr) {
      trim(arr);
      var length = arr.length;
      if (length < 4 && compareAbs(arr, MAX_INT_ARR) < 0) {
          switch (length) {
              case 0:
                  return 0;
              case 1:
                  return arr[0];
              case 2:
                  return arr[0] + arr[1] * BASE;
              default:
                  return arr[0] + (arr[1] + arr[2] * BASE) * BASE
          }
      }
      return arr
  }

  function trim(v) {
      var i = v.length;
      while (v[--i] === 0);
      v.length = i + 1
  }

  function createArray(length) {
      var x = new Array(length);
      var i = -1;
      while (++i < length) {
          x[i] = 0
      }
      return x
  }

  function truncate(n) {
      if (n > 0) return Math.floor(n);
      return Math.ceil(n)
  }

  function add(a, b) { // benz
      var l_a = a.length,
          l_b = b.length,
          r = new Array(l_a),
          carry = 0,
          base = BASE,
          sum, i;
      for (i = 0; i < l_b; i++) {
          sum = a[i] + b[i] + carry;
          carry = sum >= base ? 1 : 0;
          r[i] = sum - carry * base
      }
      while (i < l_a) {
          sum = a[i] + carry;
          carry = sum === base ? 1 : 0;
          r[i++] = sum - carry * base
      }
      if (carry > 0) r.push(carry);
      return r
  }

  function addAny(a, b) {
      if (a.length >= b.length) return add(a, b);
      return add(b, a)
  }

  function addSmall(a, carry) {
      var l = a.length,
          r = new Array(l),
          base = BASE,
          sum, i;
      for (i = 0; i < l; i++) {
          sum = a[i] - base + carry;
          carry = Math.floor(sum / base);
          r[i] = sum - carry * base;
          carry += 1
      }
      while (carry > 0) {
          r[i++] = carry % base;
          carry = Math.floor(carry / base)
      }
      return r
  }
  BigInteger.prototype.add = function(v) {
      var n = parseValue(v);
      if (this.sign !== n.sign) {
          return this.subtract(n.negate())
      }
      var a = this.value,
          b = n.value;
      if (n.isSmall) {
          return new BigInteger(addSmall(a, Math.abs(b)), this.sign)
      }
      return new BigInteger(addAny(a, b), this.sign)
  };
  BigInteger.prototype.plus = BigInteger.prototype.add;
  SmallInteger.prototype.add = function(v) {
      var n = parseValue(v);
      var a = this.value;
      if (a < 0 !== n.sign) {
          return this.subtract(n.negate())
      }
      var b = n.value;
      if (n.isSmall) {
          if (isPrecise(a + b)) return new SmallInteger(a + b);
          b = smallToArray(Math.abs(b))
      }
      return new BigInteger(addSmall(b, Math.abs(a)), a < 0)
  };
  SmallInteger.prototype.plus = SmallInteger.prototype.add;
  NativeBigInt.prototype.add = function(v) {
      return new NativeBigInt(this.value + parseValue(v).value)
  };
  NativeBigInt.prototype.plus = NativeBigInt.prototype.add;

  function subtract(a, b) {
      var a_l = a.length,
          b_l = b.length,
          r = new Array(a_l),
          borrow = 0,
          base = BASE,
          i, difference;
      for (i = 0; i < b_l; i++) {
          difference = a[i] - borrow - b[i];
          if (difference < 0) {
              difference += base;
              borrow = 1
          } else borrow = 0;
          r[i] = difference
      }
      for (i = b_l; i < a_l; i++) {
          difference = a[i] - borrow;
          if (difference < 0) difference += base;
          else {
              r[i++] = difference;
              break
          }
          r[i] = difference
      }
      for (; i < a_l; i++) {
          r[i] = a[i]
      }
      trim(r);
      return r
  }

  function subtractAny(a, b, sign) {
      var value;
      if (compareAbs(a, b) >= 0) {
          value = subtract(a, b)
      } else {
          value = subtract(b, a);
          sign = !sign
      }
      value = arrayToSmall(value);
      if (typeof value === "number") {
          if (sign) value = -value;
          return new SmallInteger(value)
      }
      return new BigInteger(value, sign)
  }

  function subtractSmall(a, b, sign) {
      var l = a.length,
          r = new Array(l),
          carry = -b,
          base = BASE,
          i, difference;
      for (i = 0; i < l; i++) {
          difference = a[i] + carry;
          carry = Math.floor(difference / base);
          difference %= base;
          r[i] = difference < 0 ? difference + base : difference
      }
      r = arrayToSmall(r);
      if (typeof r === "number") {
          if (sign) r = -r;
          return new SmallInteger(r)
      }
      return new BigInteger(r, sign)
  }
  BigInteger.prototype.subtract = function(v) {
      var n = parseValue(v);
      if (this.sign !== n.sign) {
          return this.add(n.negate())
      }
      var a = this.value,
          b = n.value;
      if (n.isSmall) return subtractSmall(a, Math.abs(b), this.sign);
      return subtractAny(a, b, this.sign)
  };
  BigInteger.prototype.minus = BigInteger.prototype.subtract;
  SmallInteger.prototype.subtract = function(v) {
      var n = parseValue(v);
      var a = this.value;
      if (a < 0 !== n.sign) {
          return this.add(n.negate())
      }
      var b = n.value;
      if (n.isSmall) {
          return new SmallInteger(a - b)
      }
      return subtractSmall(b, Math.abs(a), a >= 0)
  };
  SmallInteger.prototype.minus = SmallInteger.prototype.subtract;
  NativeBigInt.prototype.subtract = function(v) {
      return new NativeBigInt(this.value - parseValue(v).value)
  };
  NativeBigInt.prototype.minus = NativeBigInt.prototype.subtract;
  BigInteger.prototype.negate = function() {
      return new BigInteger(this.value, !this.sign)
  };
  SmallInteger.prototype.negate = function() {
      var sign = this.sign;
      var small = new SmallInteger(-this.value);
      small.sign = !sign;
      return small
  };
  NativeBigInt.prototype.negate = function() {
      return new NativeBigInt(-this.value)
  };
  BigInteger.prototype.abs = function() {
      return new BigInteger(this.value, false)
  };
  SmallInteger.prototype.abs = function() {
      return new SmallInteger(Math.abs(this.value))
  };
  NativeBigInt.prototype.abs = function() {
      return new NativeBigInt(this.value >= 0 ? this.value : -this.value)
  };

  function multiplyLong(a, b) {
      var a_l = a.length,
          b_l = b.length,
          l = a_l + b_l,
          r = createArray(l),
          base = BASE,
          product, carry, i, a_i, b_j;
      for (i = 0; i < a_l; ++i) {
          a_i = a[i];
          for (var j = 0; j < b_l; ++j) {
              b_j = b[j];
              product = a_i * b_j + r[i + j];
              carry = Math.floor(product / base);
              r[i + j] = product - carry * base;
              r[i + j + 1] += carry
          }
      }
      trim(r);
      return r
  }

  function multiplySmall(a, b) {
      var l = a.length,
          r = new Array(l),
          base = BASE,
          carry = 0,
          product, i;
      for (i = 0; i < l; i++) {
          product = a[i] * b + carry;
          carry = Math.floor(product / base);
          r[i] = product - carry * base
      }
      while (carry > 0) {
          r[i++] = carry % base;
          carry = Math.floor(carry / base)
      }
      return r
  }

  function shiftLeft(x, n) {
      var r = [];
      while (n-- > 0) r.push(0);
      return r.concat(x)
  }

  function multiplyKaratsuba(x, y) {
      var n = Math.max(x.length, y.length);
      if (n <= 30) return multiplyLong(x, y);
      n = Math.ceil(n / 2);
      var b = x.slice(n),
          a = x.slice(0, n),
          d = y.slice(n),
          c = y.slice(0, n);
      var ac = multiplyKaratsuba(a, c),
          bd = multiplyKaratsuba(b, d),
          abcd = multiplyKaratsuba(addAny(a, b), addAny(c, d));
      var product = addAny(addAny(ac, shiftLeft(subtract(subtract(abcd, ac), bd), n)), shiftLeft(bd, 2 * n));
      trim(product);
      return product
  }

  function useKaratsuba(l1, l2) {
      return -.012 * l1 - .012 * l2 + 15e-6 * l1 * l2 > 0
  }
  BigInteger.prototype.multiply = function(v) { // benz
      var n = parseValue(v),
          a = this.value,
          b = n.value,
          sign = this.sign !== n.sign,
          abs;
      if (n.isSmall) {
          if (b === 0) return Integer[0];
          if (b === 1) return this;
          if (b === -1) return this.negate();
          abs = Math.abs(b);
          if (abs < BASE) {
              return new BigInteger(multiplySmall(a, abs), sign)
          }
          b = smallToArray(abs)
      }
      if (useKaratsuba(a.length, b.length)) return new BigInteger(multiplyKaratsuba(a, b), sign);
      return new BigInteger(multiplyLong(a, b), sign)
  };
  BigInteger.prototype.times = BigInteger.prototype.multiply;

  function multiplySmallAndArray(a, b, sign) {
      if (a < BASE) {
          return new BigInteger(multiplySmall(b, a), sign)
      }
      return new BigInteger(multiplyLong(b, smallToArray(a)), sign)
  }
  SmallInteger.prototype._multiplyBySmall = function(a) {
      if (isPrecise(a.value * this.value)) {
          return new SmallInteger(a.value * this.value)
      }
      return multiplySmallAndArray(Math.abs(a.value), smallToArray(Math.abs(this.value)), this.sign !== a.sign)
  };
  BigInteger.prototype._multiplyBySmall = function(a) {
      if (a.value === 0) return Integer[0];
      if (a.value === 1) return this;
      if (a.value === -1) return this.negate();
      return multiplySmallAndArray(Math.abs(a.value), this.value, this.sign !== a.sign)
  };
  SmallInteger.prototype.multiply = function(v) {
      return parseValue(v)._multiplyBySmall(this)
  };
  SmallInteger.prototype.times = SmallInteger.prototype.multiply;
  NativeBigInt.prototype.multiply = function(v) {
      return new NativeBigInt(this.value * parseValue(v).value)
  };
  NativeBigInt.prototype.times = NativeBigInt.prototype.multiply;

  function square(a) {
      var l = a.length,
          r = createArray(l + l),
          base = BASE,
          product, carry, i, a_i, a_j;
      for (i = 0; i < l; i++) {
          a_i = a[i];
          carry = 0 - a_i * a_i;
          for (var j = i; j < l; j++) {
              a_j = a[j];
              product = 2 * (a_i * a_j) + r[i + j] + carry;
              carry = Math.floor(product / base);
              r[i + j] = product - carry * base
          }
          r[i + l] = carry
      }
      trim(r);
      return r
  }
  BigInteger.prototype.square = function() {
      return new BigInteger(square(this.value), false)
  };
  SmallInteger.prototype.square = function() {
      var value = this.value * this.value;
      if (isPrecise(value)) return new SmallInteger(value);
      return new BigInteger(square(smallToArray(Math.abs(this.value))), false)
  };
  NativeBigInt.prototype.square = function(v) {
      return new NativeBigInt(this.value * this.value)
  };

  function divMod1(a, b) {
      var a_l = a.length,
          b_l = b.length,
          base = BASE,
          result = createArray(b.length),
          divisorMostSignificantDigit = b[b_l - 1],
          lambda = Math.ceil(base / (2 * divisorMostSignificantDigit)),
          remainder = multiplySmall(a, lambda),
          divisor = multiplySmall(b, lambda),
          quotientDigit, shift, carry, borrow, i, l, q;
      if (remainder.length <= a_l) remainder.push(0);
      divisor.push(0);
      divisorMostSignificantDigit = divisor[b_l - 1];
      for (shift = a_l - b_l; shift >= 0; shift--) {
          quotientDigit = base - 1;
          if (remainder[shift + b_l] !== divisorMostSignificantDigit) {
              quotientDigit = Math.floor((remainder[shift + b_l] * base + remainder[shift + b_l - 1]) / divisorMostSignificantDigit)
          }
          carry = 0;
          borrow = 0;
          l = divisor.length;
          for (i = 0; i < l; i++) {
              carry += quotientDigit * divisor[i];
              q = Math.floor(carry / base);
              borrow += remainder[shift + i] - (carry - q * base);
              carry = q;
              if (borrow < 0) {
                  remainder[shift + i] = borrow + base;
                  borrow = -1
              } else {
                  remainder[shift + i] = borrow;
                  borrow = 0
              }
          }
          while (borrow !== 0) {
              quotientDigit -= 1;
              carry = 0;
              for (i = 0; i < l; i++) {
                  carry += remainder[shift + i] - base + divisor[i];
                  if (carry < 0) {
                      remainder[shift + i] = carry + base;
                      carry = 0
                  } else {
                      remainder[shift + i] = carry;
                      carry = 1
                  }
              }
              borrow += carry
          }
          result[shift] = quotientDigit
      }
      remainder = divModSmall(remainder, lambda)[0];
      return [arrayToSmall(result), arrayToSmall(remainder)]
  }

  function divMod2(a, b) {
      var a_l = a.length,
          b_l = b.length,
          result = [],
          part = [],
          base = BASE,
          guess, xlen, highx, highy, check;
      while (a_l) {
          part.unshift(a[--a_l]);
          trim(part);
          if (compareAbs(part, b) < 0) {
              result.push(0);
              continue
          }
          xlen = part.length;
          highx = part[xlen - 1] * base + part[xlen - 2];
          highy = b[b_l - 1] * base + b[b_l - 2];
          if (xlen > b_l) {
              highx = (highx + 1) * base
          }
          guess = Math.ceil(highx / highy);
          do {
              check = multiplySmall(b, guess);
              if (compareAbs(check, part) <= 0) break;
              guess--
          } while (guess);
          result.push(guess);
          part = subtract(part, check)
      }
      result.reverse();
      return [arrayToSmall(result), arrayToSmall(part)]
  }

  function divModSmall(value, lambda) {
      var length = value.length,
          quotient = createArray(length),
          base = BASE,
          i, q, remainder, divisor;
      remainder = 0;
      for (i = length - 1; i >= 0; --i) {
          divisor = remainder * base + value[i];
          q = truncate(divisor / lambda);
          remainder = divisor - q * lambda;
          quotient[i] = q | 0
      }
      return [quotient, remainder | 0]
  }

  function divModAny(self, v) {
      var value, n = parseValue(v);
      if (supportsNativeBigInt) {
          return [new NativeBigInt(self.value / n.value), new NativeBigInt(self.value % n.value)]
      }
      var a = self.value,
          b = n.value;
      var quotient;
      if (b === 0) throw new Error("Cannot divide by zero");
      if (self.isSmall) {
          if (n.isSmall) {
              return [new SmallInteger(truncate(a / b)), new SmallInteger(a % b)]
          }
          return [Integer[0], self]
      }
      if (n.isSmall) {
          if (b === 1) return [self, Integer[0]];
          if (b == -1) return [self.negate(), Integer[0]];
          var abs = Math.abs(b);
          if (abs < BASE) {
              value = divModSmall(a, abs);
              quotient = arrayToSmall(value[0]);
              var remainder = value[1];
              if (self.sign) remainder = -remainder;
              if (typeof quotient === "number") {
                  if (self.sign !== n.sign) quotient = -quotient;
                  return [new SmallInteger(quotient), new SmallInteger(remainder)]
              }
              return [new BigInteger(quotient, self.sign !== n.sign), new SmallInteger(remainder)]
          }
          b = smallToArray(abs)
      }
      var comparison = compareAbs(a, b);
      if (comparison === -1) return [Integer[0], self];
      if (comparison === 0) return [Integer[self.sign === n.sign ? 1 : -1], Integer[0]];
      if (a.length + b.length <= 200) value = divMod1(a, b);
      else value = divMod2(a, b);
      quotient = value[0];
      var qSign = self.sign !== n.sign,
          mod = value[1],
          mSign = self.sign;
      if (typeof quotient === "number") {
          if (qSign) quotient = -quotient;
          quotient = new SmallInteger(quotient)
      } else quotient = new BigInteger(quotient, qSign);
      if (typeof mod === "number") {
          if (mSign) mod = -mod;
          mod = new SmallInteger(mod)
      } else mod = new BigInteger(mod, mSign);
      return [quotient, mod]
  }
  BigInteger.prototype.divmod = function(v) {
      var result = divModAny(this, v);
      return {
          quotient: result[0],
          remainder: result[1]
      }
  };
  NativeBigInt.prototype.divmod = SmallInteger.prototype.divmod = BigInteger.prototype.divmod;
  BigInteger.prototype.divide = function(v) {
      return divModAny(this, v)[0]
  };
  NativeBigInt.prototype.over = NativeBigInt.prototype.divide = function(v) {
      return new NativeBigInt(this.value / parseValue(v).value)
  };
  SmallInteger.prototype.over = SmallInteger.prototype.divide = BigInteger.prototype.over = BigInteger.prototype.divide;
  BigInteger.prototype.mod = function(v) {
      return divModAny(this, v)[1]
  };
  NativeBigInt.prototype.mod = NativeBigInt.prototype.remainder = function(v) {
      return new NativeBigInt(this.value % parseValue(v).value)
  };
  SmallInteger.prototype.remainder = SmallInteger.prototype.mod = BigInteger.prototype.remainder = BigInteger.prototype.mod;
  BigInteger.prototype.pow = function(v) {
      var n = parseValue(v),
          a = this.value,
          b = n.value,
          value, x, y;
      if (b === 0) return Integer[1];
      if (a === 0) return Integer[0];
      if (a === 1) return Integer[1];
      if (a === -1) return n.isEven() ? Integer[1] : Integer[-1];
      if (n.sign) {
          return Integer[0]
      }
      if (!n.isSmall) throw new Error("The exponent " + n.toString() + " is too large.");
      if (this.isSmall) {
          if (isPrecise(value = Math.pow(a, b))) return new SmallInteger(truncate(value))
      }
      x = this;
      y = Integer[1];
      while (true) {
          if (b & 1 === 1) {
              y = y.times(x);
              --b
          }
          if (b === 0) break;
          b /= 2;
          x = x.square()
      }
      return y
  };
  SmallInteger.prototype.pow = BigInteger.prototype.pow;
  NativeBigInt.prototype.pow = function(v) {
      var n = parseValue(v);
      var a = this.value,
          b = n.value;
      var _0 = BigInt(0),
          _1 = BigInt(1),
          _2 = BigInt(2);
      if (b === _0) return Integer[1];
      if (a === _0) return Integer[0];
      if (a === _1) return Integer[1];
      if (a === BigInt(-1)) return n.isEven() ? Integer[1] : Integer[-1];
      if (n.isNegative()) return new NativeBigInt(_0);
      var x = this;
      var y = Integer[1];
      while (true) {
          if ((b & _1) === _1) {
              y = y.times(x);
              --b
          }
          if (b === _0) break;
          b /= _2;
          x = x.square()
      }
      return y
  };
  BigInteger.prototype.modPow = function(exp, mod) {
      exp = parseValue(exp);
      mod = parseValue(mod);
      if (mod.isZero()) throw new Error("Cannot take modPow with modulus 0");
      var r = Integer[1],
          base = this.mod(mod);
      while (exp.isPositive()) {
          if (base.isZero()) return Integer[0];
          if (exp.isOdd()) r = r.multiply(base).mod(mod);
          exp = exp.divide(2);
          base = base.square().mod(mod)
      }
      return r
  };
  NativeBigInt.prototype.modPow = SmallInteger.prototype.modPow = BigInteger.prototype.modPow;

  function compareAbs(a, b) {
      if (a.length !== b.length) {
          return a.length > b.length ? 1 : -1
      }
      for (var i = a.length - 1; i >= 0; i--) {
          if (a[i] !== b[i]) return a[i] > b[i] ? 1 : -1
      }
      return 0
  }
  BigInteger.prototype.compareAbs = function(v) {
      var n = parseValue(v),
          a = this.value,
          b = n.value;
      if (n.isSmall) return 1;
      return compareAbs(a, b)
  };
  SmallInteger.prototype.compareAbs = function(v) {
      var n = parseValue(v),
          a = Math.abs(this.value),
          b = n.value;
      if (n.isSmall) {
          b = Math.abs(b);
          return a === b ? 0 : a > b ? 1 : -1
      }
      return -1
  };
  NativeBigInt.prototype.compareAbs = function(v) {
      var a = this.value;
      var b = parseValue(v).value;
      a = a >= 0 ? a : -a;
      b = b >= 0 ? b : -b;
      return a === b ? 0 : a > b ? 1 : -1
  };
  BigInteger.prototype.compare = function(v) {
      if (v === Infinity) {
          return -1
      }
      if (v === -Infinity) {
          return 1
      }
      var n = parseValue(v),
          a = this.value,
          b = n.value;
      if (this.sign !== n.sign) {
          return n.sign ? 1 : -1
      }
      if (n.isSmall) {
          return this.sign ? -1 : 1
      }
      return compareAbs(a, b) * (this.sign ? -1 : 1)
  };
  BigInteger.prototype.compareTo = BigInteger.prototype.compare;
  SmallInteger.prototype.compare = function(v) {
      if (v === Infinity) {
          return -1
      }
      if (v === -Infinity) {
          return 1
      }
      var n = parseValue(v),
          a = this.value,
          b = n.value;
      if (n.isSmall) {
          return a == b ? 0 : a > b ? 1 : -1
      }
      if (a < 0 !== n.sign) {
          return a < 0 ? -1 : 1
      }
      return a < 0 ? 1 : -1
  };
  SmallInteger.prototype.compareTo = SmallInteger.prototype.compare;
  NativeBigInt.prototype.compare = function(v) {
      if (v === Infinity) {
          return -1
      }
      if (v === -Infinity) {
          return 1
      }
      var a = this.value;
      var b = parseValue(v).value;
      return a === b ? 0 : a > b ? 1 : -1
  };
  NativeBigInt.prototype.compareTo = NativeBigInt.prototype.compare;
  BigInteger.prototype.equals = function(v) {
      return this.compare(v) === 0
  };
  NativeBigInt.prototype.eq = NativeBigInt.prototype.equals = SmallInteger.prototype.eq = SmallInteger.prototype.equals = BigInteger.prototype.eq = BigInteger.prototype.equals;
  BigInteger.prototype.notEquals = function(v) {
      return this.compare(v) !== 0
  };
  NativeBigInt.prototype.neq = NativeBigInt.prototype.notEquals = SmallInteger.prototype.neq = SmallInteger.prototype.notEquals = BigInteger.prototype.neq = BigInteger.prototype.notEquals;
  BigInteger.prototype.greater = function(v) {
      return this.compare(v) > 0
  };
  NativeBigInt.prototype.gt = NativeBigInt.prototype.greater = SmallInteger.prototype.gt = SmallInteger.prototype.greater = BigInteger.prototype.gt = BigInteger.prototype.greater;
  BigInteger.prototype.lesser = function(v) {
      return this.compare(v) < 0
  };
  NativeBigInt.prototype.lt = NativeBigInt.prototype.lesser = SmallInteger.prototype.lt = SmallInteger.prototype.lesser = BigInteger.prototype.lt = BigInteger.prototype.lesser;
  BigInteger.prototype.greaterOrEquals = function(v) {
      return this.compare(v) >= 0
  };
  NativeBigInt.prototype.geq = NativeBigInt.prototype.greaterOrEquals = SmallInteger.prototype.geq = SmallInteger.prototype.greaterOrEquals = BigInteger.prototype.geq = BigInteger.prototype.greaterOrEquals;
  BigInteger.prototype.lesserOrEquals = function(v) {
      return this.compare(v) <= 0
  };
  NativeBigInt.prototype.leq = NativeBigInt.prototype.lesserOrEquals = SmallInteger.prototype.leq = SmallInteger.prototype.lesserOrEquals = BigInteger.prototype.leq = BigInteger.prototype.lesserOrEquals;
  BigInteger.prototype.isEven = function() {
      return (this.value[0] & 1) === 0
  };
  SmallInteger.prototype.isEven = function() {
      return (this.value & 1) === 0
  };
  NativeBigInt.prototype.isEven = function() {
      return (this.value & BigInt(1)) === BigInt(0)
  };
  BigInteger.prototype.isOdd = function() {
      return (this.value[0] & 1) === 1
  };
  SmallInteger.prototype.isOdd = function() {
      return (this.value & 1) === 1
  };
  NativeBigInt.prototype.isOdd = function() {
      return (this.value & BigInt(1)) === BigInt(1)
  };
  BigInteger.prototype.isPositive = function() {
      return !this.sign
  };
  SmallInteger.prototype.isPositive = function() {
      return this.value > 0
  };
  NativeBigInt.prototype.isPositive = SmallInteger.prototype.isPositive;
  BigInteger.prototype.isNegative = function() {
      return this.sign
  };
  SmallInteger.prototype.isNegative = function() {
      return this.value < 0
  };
  NativeBigInt.prototype.isNegative = SmallInteger.prototype.isNegative;
  BigInteger.prototype.isUnit = function() {
      return false
  };
  SmallInteger.prototype.isUnit = function() {
      return Math.abs(this.value) === 1
  };
  NativeBigInt.prototype.isUnit = function() {
      return this.abs().value === BigInt(1)
  };
  BigInteger.prototype.isZero = function() {
      return false
  };
  SmallInteger.prototype.isZero = function() {
      return this.value === 0
  };
  NativeBigInt.prototype.isZero = function() {
      return this.value === BigInt(0)
  };
  BigInteger.prototype.isDivisibleBy = function(v) {
      var n = parseValue(v);
      if (n.isZero()) return false;
      if (n.isUnit()) return true;
      if (n.compareAbs(2) === 0) return this.isEven();
      return this.mod(n).isZero()
  };
  NativeBigInt.prototype.isDivisibleBy = SmallInteger.prototype.isDivisibleBy = BigInteger.prototype.isDivisibleBy;

  function isBasicPrime(v) {
      var n = v.abs();
      if (n.isUnit()) return false;
      if (n.equals(2) || n.equals(3) || n.equals(5)) return true;
      if (n.isEven() || n.isDivisibleBy(3) || n.isDivisibleBy(5)) return false;
      if (n.lesser(49)) return true
  }

  function millerRabinTest(n, a) {
      var nPrev = n.prev(),
          b = nPrev,
          r = 0,
          d, t, i, x;
      while (b.isEven()) b = b.divide(2), r++;
      next: for (i = 0; i < a.length; i++) {
          if (n.lesser(a[i])) continue;
          x = bigInt(a[i]).modPow(b, n);
          if (x.isUnit() || x.equals(nPrev)) continue;
          for (d = r - 1; d != 0; d--) {
              x = x.square().mod(n);
              if (x.isUnit()) return false;
              if (x.equals(nPrev)) continue next
          }
          return false
      }
      return true
  }
  BigInteger.prototype.isPrime = function(strict) {
      var isPrime = isBasicPrime(this);
      if (isPrime !== undefined) return isPrime;
      var n = this.abs();
      var bits = n.bitLength();
      if (bits <= 64) return millerRabinTest(n, [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]);
      var logN = Math.log(2) * bits.toJSNumber();
      var t = Math.ceil(strict === true ? 2 * Math.pow(logN, 2) : logN);
      for (var a = [], i = 0; i < t; i++) {
          a.push(bigInt(i + 2))
      }
      return millerRabinTest(n, a)
  };
  NativeBigInt.prototype.isPrime = SmallInteger.prototype.isPrime = BigInteger.prototype.isPrime;
  BigInteger.prototype.isProbablePrime = function(iterations) {
      var isPrime = isBasicPrime(this);
      if (isPrime !== undefined) return isPrime;
      var n = this.abs();
      var t = iterations === undefined ? 5 : iterations;
      for (var a = [], i = 0; i < t; i++) {
          a.push(bigInt.randBetween(2, n.minus(2)))
      }
      return millerRabinTest(n, a)
  };
  NativeBigInt.prototype.isProbablePrime = SmallInteger.prototype.isProbablePrime = BigInteger.prototype.isProbablePrime;
  BigInteger.prototype.modInv = function(n) {
      var t = bigInt.zero,
          newT = bigInt.one,
          r = parseValue(n),
          newR = this.abs(),
          q, lastT, lastR;
      while (!newR.isZero()) {
          q = r.divide(newR);
          lastT = t;
          lastR = r;
          t = newT;
          r = newR;
          newT = lastT.subtract(q.multiply(newT));
          newR = lastR.subtract(q.multiply(newR))
      }
      if (!r.isUnit()) throw new Error(this.toString() + " and " + n.toString() + " are not co-prime");
      if (t.compare(0) === -1) {
          t = t.add(n)
      }
      if (this.isNegative()) {
          return t.negate()
      }
      return t
  };
  NativeBigInt.prototype.modInv = SmallInteger.prototype.modInv = BigInteger.prototype.modInv;
  BigInteger.prototype.next = function() {
      var value = this.value;
      if (this.sign) {
          return subtractSmall(value, 1, this.sign)
      }
      return new BigInteger(addSmall(value, 1), this.sign)
  };
  SmallInteger.prototype.next = function() {
      var value = this.value;
      if (value + 1 < MAX_INT) return new SmallInteger(value + 1);
      return new BigInteger(MAX_INT_ARR, false)
  };
  NativeBigInt.prototype.next = function() {
      return new NativeBigInt(this.value + BigInt(1))
  };
  BigInteger.prototype.prev = function() {
      var value = this.value;
      if (this.sign) {
          return new BigInteger(addSmall(value, 1), true)
      }
      return subtractSmall(value, 1, this.sign)
  };
  SmallInteger.prototype.prev = function() {
      var value = this.value;
      if (value - 1 > -MAX_INT) return new SmallInteger(value - 1);
      return new BigInteger(MAX_INT_ARR, true)
  };
  NativeBigInt.prototype.prev = function() {
      return new NativeBigInt(this.value - BigInt(1))
  };
  var powersOfTwo = [1];
  while (2 * powersOfTwo[powersOfTwo.length - 1] <= BASE) powersOfTwo.push(2 * powersOfTwo[powersOfTwo.length - 1]);
  var powers2Length = powersOfTwo.length,
      highestPower2 = powersOfTwo[powers2Length - 1];

  function shift_isSmall(n) {
      return Math.abs(n) <= BASE
  }
  BigInteger.prototype.shiftLeft = function(v) {
      var n = parseValue(v).toJSNumber();
      if (!shift_isSmall(n)) {
          throw new Error(String(n) + " is too large for shifting.")
      }
      if (n < 0) return this.shiftRight(-n);
      var result = this;
      if (result.isZero()) return result;
      while (n >= powers2Length) {
          result = result.multiply(highestPower2);
          n -= powers2Length - 1
      }
      return result.multiply(powersOfTwo[n])
  };
  NativeBigInt.prototype.shiftLeft = SmallInteger.prototype.shiftLeft = BigInteger.prototype.shiftLeft;
  BigInteger.prototype.shiftRight = function(v) {
      var remQuo;
      var n = parseValue(v).toJSNumber();
      if (!shift_isSmall(n)) {
          throw new Error(String(n) + " is too large for shifting.")
      }
      if (n < 0) return this.shiftLeft(-n);
      var result = this;
      while (n >= powers2Length) {
          if (result.isZero() || result.isNegative() && result.isUnit()) return result;
          remQuo = divModAny(result, highestPower2);
          result = remQuo[1].isNegative() ? remQuo[0].prev() : remQuo[0];
          n -= powers2Length - 1
      }
      remQuo = divModAny(result, powersOfTwo[n]);
      return remQuo[1].isNegative() ? remQuo[0].prev() : remQuo[0]
  };
  NativeBigInt.prototype.shiftRight = SmallInteger.prototype.shiftRight = BigInteger.prototype.shiftRight;

  function bitwise(x, y, fn) {
      y = parseValue(y);
      var xSign = x.isNegative(),
          ySign = y.isNegative();
      var xRem = xSign ? x.not() : x,
          yRem = ySign ? y.not() : y;
      var xDigit = 0,
          yDigit = 0;
      var xDivMod = null,
          yDivMod = null;
      var result = [];
      while (!xRem.isZero() || !yRem.isZero()) {
          xDivMod = divModAny(xRem, highestPower2);
          xDigit = xDivMod[1].toJSNumber();
          if (xSign) {
              xDigit = highestPower2 - 1 - xDigit
          }
          yDivMod = divModAny(yRem, highestPower2);
          yDigit = yDivMod[1].toJSNumber();
          if (ySign) {
              yDigit = highestPower2 - 1 - yDigit
          }
          xRem = xDivMod[0];
          yRem = yDivMod[0];
          result.push(fn(xDigit, yDigit))
      }
      var sum = fn(xSign ? 1 : 0, ySign ? 1 : 0) !== 0 ? bigInt(-1) : bigInt(0);
      for (var i = result.length - 1; i >= 0; i -= 1) {
          sum = sum.multiply(highestPower2).add(bigInt(result[i]))
      }
      return sum
  }
  BigInteger.prototype.not = function() {
      return this.negate().prev()
  };
  NativeBigInt.prototype.not = SmallInteger.prototype.not = BigInteger.prototype.not;
  BigInteger.prototype.and = function(n) {
      return bitwise(this, n, function(a, b) {
          return a & b
      })
  };
  NativeBigInt.prototype.and = SmallInteger.prototype.and = BigInteger.prototype.and;
  BigInteger.prototype.or = function(n) {
      return bitwise(this, n, function(a, b) {
          return a | b
      })
  };
  NativeBigInt.prototype.or = SmallInteger.prototype.or = BigInteger.prototype.or;
  BigInteger.prototype.xor = function(n) {
      return bitwise(this, n, function(a, b) {
          return a ^ b
      })
  };
  NativeBigInt.prototype.xor = SmallInteger.prototype.xor = BigInteger.prototype.xor;
  var LOBMASK_I = 1 << 30,
      LOBMASK_BI = (BASE & -BASE) * (BASE & -BASE) | LOBMASK_I;

  function roughLOB(n) {
      var v = n.value,
          x = typeof v === "number" ? v | LOBMASK_I : typeof v === "bigint" ? v | BigInt(LOBMASK_I) : v[0] + v[1] * BASE | LOBMASK_BI;
      return x & -x
  }

  function integerLogarithm(value, base) {
      if (base.compareTo(value) <= 0) {
          var tmp = integerLogarithm(value, base.square(base));
          var p = tmp.p;
          var e = tmp.e;
          var t = p.multiply(base);
          return t.compareTo(value) <= 0 ? {
              p: t,
              e: e * 2 + 1
          } : {
              p: p,
              e: e * 2
          }
      }
      return {
          p: bigInt(1),
          e: 0
      }
  }
  BigInteger.prototype.bitLength = function() {
      var n = this;
      if (n.compareTo(bigInt(0)) < 0) {
          n = n.negate().subtract(bigInt(1))
      }
      if (n.compareTo(bigInt(0)) === 0) {
          return bigInt(0)
      }
      return bigInt(integerLogarithm(n, bigInt(2)).e).add(bigInt(1))
  };
  NativeBigInt.prototype.bitLength = SmallInteger.prototype.bitLength = BigInteger.prototype.bitLength;

  function max(a, b) {
      a = parseValue(a);
      b = parseValue(b);
      return a.greater(b) ? a : b
  }

  function min(a, b) {
      a = parseValue(a);
      b = parseValue(b);
      return a.lesser(b) ? a : b
  }

  function gcd(a, b) {
      a = parseValue(a).abs();
      b = parseValue(b).abs();
      if (a.equals(b)) return a;
      if (a.isZero()) return b;
      if (b.isZero()) return a;
      var c = Integer[1],
          d, t;
      while (a.isEven() && b.isEven()) {
          d = min(roughLOB(a), roughLOB(b));
          a = a.divide(d);
          b = b.divide(d);
          c = c.multiply(d)
      }
      while (a.isEven()) {
          a = a.divide(roughLOB(a))
      }
      do {
          while (b.isEven()) {
              b = b.divide(roughLOB(b))
          }
          if (a.greater(b)) {
              t = b;
              b = a;
              a = t
          }
          b = b.subtract(a)
      } while (!b.isZero());
      return c.isUnit() ? a : a.multiply(c)
  }

  function lcm(a, b) {
      a = parseValue(a).abs();
      b = parseValue(b).abs();
      return a.divide(gcd(a, b)).multiply(b)
  }

  function randBetween(a, b) {
      a = parseValue(a);
      b = parseValue(b);
      var low = min(a, b),
          high = max(a, b);
      var range = high.subtract(low).add(1);
      if (range.isSmall) return low.add(Math.floor(Math.random() * range));
      var digits = toBase(range, BASE).value;
      var result = [],
          restricted = true;
      for (var i = 0; i < digits.length; i++) {
          var top = restricted ? digits[i] : BASE;
          var digit = truncate(Math.random() * top);
          result.push(digit);
          if (digit < top) restricted = false
      }
      return low.add(Integer.fromArray(result, BASE, false))
  }
  var parseBase = function(text, base, alphabet, caseSensitive) {
      alphabet = alphabet || DEFAULT_ALPHABET;
      text = String(text);
      if (!caseSensitive) {
          text = text.toLowerCase();
          alphabet = alphabet.toLowerCase()
      }
      var length = text.length;
      var i;
      var absBase = Math.abs(base);
      var alphabetValues = {};
      for (i = 0; i < alphabet.length; i++) {
          alphabetValues[alphabet[i]] = i
      }
      for (i = 0; i < length; i++) {
          var c = text[i];
          if (c === "-") continue;
          if (c in alphabetValues) {
              if (alphabetValues[c] >= absBase) {
                  if (c === "1" && absBase === 1) continue;
                  throw new Error(c + " is not a valid digit in base " + base + ".")
              }
          }
      }
      base = parseValue(base);
      var digits = [];
      var isNegative = text[0] === "-";
      for (i = isNegative ? 1 : 0; i < text.length; i++) {
          var c = text[i];
          if (c in alphabetValues) digits.push(parseValue(alphabetValues[c]));
          else if (c === "<") {
              var start = i;
              do {
                  i++
              } while (text[i] !== ">" && i < text.length);
              digits.push(parseValue(text.slice(start + 1, i)))
          } else throw new Error(c + " is not a valid character")
      }
      return parseBaseFromArray(digits, base, isNegative)
  };

  function parseBaseFromArray(digits, base, isNegative) {
      var val = Integer[0],
          pow = Integer[1],
          i;
      for (i = digits.length - 1; i >= 0; i--) {
          val = val.add(digits[i].times(pow));
          pow = pow.times(base)
      }
      return isNegative ? val.negate() : val
  }

  function stringify(digit, alphabet) {
      alphabet = alphabet || DEFAULT_ALPHABET;
      if (digit < alphabet.length) {
          return alphabet[digit]
      }
      return "<" + digit + ">"
  }

  function toBase(n, base) {
      base = bigInt(base);
      if (base.isZero()) {
          if (n.isZero()) return {
              value: [0],
              isNegative: false
          };
          throw new Error("Cannot convert nonzero numbers to base 0.")
      }
      if (base.equals(-1)) {
          if (n.isZero()) return {
              value: [0],
              isNegative: false
          };
          if (n.isNegative()) return {
              value: [].concat.apply([], Array.apply(null, Array(-n.toJSNumber())).map(Array.prototype.valueOf, [1, 0])),
              isNegative: false
          };
          var arr = Array.apply(null, Array(n.toJSNumber() - 1)).map(Array.prototype.valueOf, [0, 1]);
          arr.unshift([1]);
          return {
              value: [].concat.apply([], arr),
              isNegative: false
          }
      }
      var neg = false;
      if (n.isNegative() && base.isPositive()) {
          neg = true;
          n = n.abs()
      }
      if (base.isUnit()) {
          if (n.isZero()) return {
              value: [0],
              isNegative: false
          };
          return {
              value: Array.apply(null, Array(n.toJSNumber())).map(Number.prototype.valueOf, 1),
              isNegative: neg
          }
      }
      var out = [];
      var left = n,
          divmod;
      while (left.isNegative() || left.compareAbs(base) >= 0) {
          divmod = left.divmod(base);
          left = divmod.quotient;
          var digit = divmod.remainder;
          if (digit.isNegative()) {
              digit = base.minus(digit).abs();
              left = left.next()
          }
          out.push(digit.toJSNumber())
      }
      out.push(left.toJSNumber());
      return {
          value: out.reverse(),
          isNegative: neg
      }
  }

  function toBaseString(n, base, alphabet) {
      var arr = toBase(n, base);
      return (arr.isNegative ? "-" : "") + arr.value.map(function(x) {
          return stringify(x, alphabet)
      }).join("")
  }
  BigInteger.prototype.toArray = function(radix) {
      return toBase(this, radix)
  };
  SmallInteger.prototype.toArray = function(radix) {
      return toBase(this, radix)
  };
  NativeBigInt.prototype.toArray = function(radix) {
      return toBase(this, radix)
  };
  BigInteger.prototype.toString = function(radix, alphabet) {
      if (radix === undefined) radix = 10;
      if (radix !== 10) return toBaseString(this, radix, alphabet);
      var v = this.value,
          l = v.length,
          str = String(v[--l]),
          zeros = "0000000",
          digit;
      while (--l >= 0) {
          digit = String(v[l]);
          str += zeros.slice(digit.length) + digit
      }
      var sign = this.sign ? "-" : "";
      return sign + str
  };
  SmallInteger.prototype.toString = function(radix, alphabet) {
      if (radix === undefined) radix = 10;
      if (radix != 10) return toBaseString(this, radix, alphabet);
      return String(this.value)
  };
  NativeBigInt.prototype.toString = SmallInteger.prototype.toString;
  NativeBigInt.prototype.toJSON = BigInteger.prototype.toJSON = SmallInteger.prototype.toJSON = function() {
      return this.toString()
  };
  BigInteger.prototype.valueOf = function() {
      return parseInt(this.toString(), 10)
  };
  BigInteger.prototype.toJSNumber = BigInteger.prototype.valueOf;
  SmallInteger.prototype.valueOf = function() {
      return this.value
  };
  SmallInteger.prototype.toJSNumber = SmallInteger.prototype.valueOf;
  NativeBigInt.prototype.valueOf = NativeBigInt.prototype.toJSNumber = function() {
      return parseInt(this.toString(), 10)
  };

  function parseStringValue(v) {
      if (isPrecise(+v)) {
          var x = +v;
          if (x === truncate(x)) return supportsNativeBigInt ? new NativeBigInt(BigInt(x)) : new SmallInteger(x);
          throw new Error("Invalid integer: " + v)
      }
      var sign = v[0] === "-";
      if (sign) v = v.slice(1);
      var split = v.split(/e/i);
      if (split.length > 2) throw new Error("Invalid integer: " + split.join("e"));
      if (split.length === 2) {
          var exp = split[1];
          if (exp[0] === "+") exp = exp.slice(1);
          exp = +exp;
          if (exp !== truncate(exp) || !isPrecise(exp)) throw new Error("Invalid integer: " + exp + " is not a valid exponent.");
          var text = split[0];
          var decimalPlace = text.indexOf(".");
          if (decimalPlace >= 0) {
              exp -= text.length - decimalPlace - 1;
              text = text.slice(0, decimalPlace) + text.slice(decimalPlace + 1)
          }
          if (exp < 0) throw new Error("Cannot include negative exponent part for integers");
          text += new Array(exp + 1).join("0");
          v = text
      }
      var isValid = /^([0-9][0-9]*)$/.test(v);
      if (!isValid) throw new Error("Invalid integer: " + v);
      if (supportsNativeBigInt) {
          return new NativeBigInt(BigInt(sign ? "-" + v : v))
      }
      var r = [],
          max = v.length,
          l = LOG_BASE,
          min = max - l;
      while (max > 0) {
          r.push(+v.slice(min, max));
          min -= l;
          if (min < 0) min = 0;
          max -= l
      }
      trim(r);
      return new BigInteger(r, sign)
  }

  function parseNumberValue(v) {
      if (supportsNativeBigInt) {
          return new NativeBigInt(BigInt(v))
      }
      if (isPrecise(v)) {
          if (v !== truncate(v)) throw new Error(v + " is not an integer.");
          return new SmallInteger(v)
      }
      return parseStringValue(v.toString())
  }

  function parseValue(v) {
      if (typeof v === "number") {
          return parseNumberValue(v)
      }
      if (typeof v === "string") {
          return parseStringValue(v)
      }
      if (typeof v === "bigint") {
          return new NativeBigInt(v)
      }
      return v
  }
  for (var i = 0; i < 1e3; i++) {
      Integer[i] = parseValue(i);
      if (i > 0) Integer[-i] = parseValue(-i)
  }
  Integer.one = Integer[1];
  Integer.zero = Integer[0];
  Integer.minusOne = Integer[-1];
  Integer.max = max;
  Integer.min = min;
  Integer.gcd = gcd;
  Integer.lcm = lcm;
  Integer.isInstance = function(x) {
      return x instanceof BigInteger || x instanceof SmallInteger || x instanceof NativeBigInt
  };
  Integer.randBetween = randBetween;
  Integer.fromArray = function(digits, base, isNegative) {
      return parseBaseFromArray(digits.map(parseValue), parseValue(base || 10), isNegative)
  };
  return Integer
}();



















/*! decimal.js-light v2.5.1 https://github.com/MikeMcl/decimal.js-light/LICENCE */
const Decimal = (function () {
  'use strict';


  /*
   *  decimal.js-light v2.5.1
   *  An arbitrary-precision Decimal type for JavaScript.
   *  https://github.com/MikeMcl/decimal.js-light
   *  Copyright (c) 2020 Michael Mclaughlin <M8ch88l@gmail.com>
   *  MIT Expat Licence
   */


  // -----------------------------------  EDITABLE DEFAULTS  ------------------------------------ //


    // The limit on the value of `precision`, and on the value of the first argument to
    // `toDecimalPlaces`, `toExponential`, `toFixed`, `toPrecision` and `toSignificantDigits`.
  var MAX_DIGITS = 1e9,                        // 0 to 1e9


    // The initial configuration properties of the Decimal constructor.
    Decimal = {

      // These values must be integers within the stated ranges (inclusive).
      // Most of these values can be changed during run-time using `Decimal.config`.

      // The maximum number of significant digits of the result of a calculation or base conversion.
      // E.g. `Decimal.config({ precision: 20 });`
      precision: 20,                         // 1 to MAX_DIGITS

      // The rounding mode used by default by `toInteger`, `toDecimalPlaces`, `toExponential`,
      // `toFixed`, `toPrecision` and `toSignificantDigits`.
      //
      // ROUND_UP         0 Away from zero.
      // ROUND_DOWN       1 Towards zero.
      // ROUND_CEIL       2 Towards +Infinity.
      // ROUND_FLOOR      3 Towards -Infinity.
      // ROUND_HALF_UP    4 Towards nearest neighbour. If equidistant, up.
      // ROUND_HALF_DOWN  5 Towards nearest neighbour. If equidistant, down.
      // ROUND_HALF_EVEN  6 Towards nearest neighbour. If equidistant, towards even neighbour.
      // ROUND_HALF_CEIL  7 Towards nearest neighbour. If equidistant, towards +Infinity.
      // ROUND_HALF_FLOOR 8 Towards nearest neighbour. If equidistant, towards -Infinity.
      //
      // E.g.
      // `Decimal.rounding = 4;`
      // `Decimal.rounding = Decimal.ROUND_HALF_UP;`
      rounding: 4,                           // 0 to 8

      // The exponent value at and beneath which `toString` returns exponential notation.
      // JavaScript numbers: -7
      toExpNeg: -7,                          // 0 to -MAX_E

      // The exponent value at and above which `toString` returns exponential notation.
      // JavaScript numbers: 21
      toExpPos:  21,                         // 0 to MAX_E

      // The natural logarithm of 10.
      // 115 digits
      LN10: '2.302585092994045684017991454684364207601101488628772976033327900967572609677352480235997205089598298341967784042286'
    },


  // ----------------------------------- END OF EDITABLE DEFAULTS ------------------------------- //


    external = true,

    decimalError = '[DecimalError] ',
    invalidArgument = decimalError + 'Invalid argument: ',
    exponentOutOfRange = decimalError + 'Exponent out of range: ',

    mathfloor = Math.floor,
    mathpow = Math.pow,

    isDecimal = /^(\d+(\.\d*)?|\.\d+)(e[+-]?\d+)?$/i,

    ONE,
    BASE = 1e7,
    LOG_BASE = 7,
    MAX_SAFE_INTEGER = 9007199254740991,
    MAX_E = mathfloor(MAX_SAFE_INTEGER / LOG_BASE),    // 1286742750677284

    // Decimal.prototype object
    P = {};


  // Decimal prototype methods


  /*
   *  absoluteValue                       abs
   *  comparedTo                          cmp
   *  decimalPlaces                       dp
   *  dividedBy                           div
   *  dividedToIntegerBy                  idiv
   *  equals                              eq
   *  exponent
   *  greaterThan                         gt
   *  greaterThanOrEqualTo                gte
   *  isInteger                           isint
   *  isNegative                          isneg
   *  isPositive                          ispos
   *  isZero
   *  lessThan                            lt
   *  lessThanOrEqualTo                   lte
   *  logarithm                           log
   *  minus                               sub
   *  modulo                              mod
   *  naturalExponential                  exp
   *  naturalLogarithm                    ln
   *  negated                             neg
   *  plus                                add
   *  precision                           sd
   *  squareRoot                          sqrt
   *  times                               mul
   *  toDecimalPlaces                     todp
   *  toExponential
   *  toFixed
   *  toInteger                           toint
   *  toNumber
   *  toPower                             pow
   *  toPrecision
   *  toSignificantDigits                 tosd
   *  toString
   *  valueOf                             val
   */


  /*
   * Return a new Decimal whose value is the absolute value of this Decimal.
   *
   */
  P.absoluteValue = P.abs = function () {
    var x = new this.constructor(this);
    if (x.s) x.s = 1;
    return x;
  };


  /*
   * Return
   *   1    if the value of this Decimal is greater than the value of `y`,
   *  -1    if the value of this Decimal is less than the value of `y`,
   *   0    if they have the same value
   *
   */
  P.comparedTo = P.cmp = function (y) {
    var i, j, xdL, ydL,
      x = this;

    y = new x.constructor(y);

    // Signs differ?
    if (x.s !== y.s) return x.s || -y.s;

    // Compare exponents.
    if (x.e !== y.e) return x.e > y.e ^ x.s < 0 ? 1 : -1;

    xdL = x.d.length;
    ydL = y.d.length;

    // Compare digit by digit.
    for (i = 0, j = xdL < ydL ? xdL : ydL; i < j; ++i) {
      if (x.d[i] !== y.d[i]) return x.d[i] > y.d[i] ^ x.s < 0 ? 1 : -1;
    }

    // Compare lengths.
    return xdL === ydL ? 0 : xdL > ydL ^ x.s < 0 ? 1 : -1;
  };


  /*
   * Return the number of decimal places of the value of this Decimal.
   *
   */
  P.decimalPlaces = P.dp = function () {
    var x = this,
      w = x.d.length - 1,
      dp = (w - x.e) * LOG_BASE;

    // Subtract the number of trailing zeros of the last word.
    w = x.d[w];
    if (w) for (; w % 10 == 0; w /= 10) dp--;

    return dp < 0 ? 0 : dp;
  };


  /*
   * Return a new Decimal whose value is the value of this Decimal divided by `y`, truncated to
   * `precision` significant digits.
   *
   */
  P.dividedBy = P.div = function (y) {
    return divide(this, new this.constructor(y));
  };


  /*
   * Return a new Decimal whose value is the integer part of dividing the value of this Decimal
   * by the value of `y`, truncated to `precision` significant digits.
   *
   */
  P.dividedToIntegerBy = P.idiv = function (y) {
    var x = this,
      Ctor = x.constructor;
    return round(divide(x, new Ctor(y), 0, 1), Ctor.precision);
  };


  /*
   * Return true if the value of this Decimal is equal to the value of `y`, otherwise return false.
   *
   */
  P.equals = P.eq = function (y) {
    return !this.cmp(y);
  };


  /*
   * Return the (base 10) exponent value of this Decimal (this.e is the base 10000000 exponent).
   *
   */
  P.exponent = function () {
    return getBase10Exponent(this);
  };


  /*
   * Return true if the value of this Decimal is greater than the value of `y`, otherwise return
   * false.
   *
   */
  P.greaterThan = P.gt = function (y) {
    return this.cmp(y) > 0;
  };


  /*
   * Return true if the value of this Decimal is greater than or equal to the value of `y`,
   * otherwise return false.
   *
   */
  P.greaterThanOrEqualTo = P.gte = function (y) {
    return this.cmp(y) >= 0;
  };


  /*
   * Return true if the value of this Decimal is an integer, otherwise return false.
   *
   */
  P.isInteger = P.isint = function () {
    return this.e > this.d.length - 2;
  };


  /*
   * Return true if the value of this Decimal is negative, otherwise return false.
   *
   */
  P.isNegative = P.isneg = function () {
    return this.s < 0;
  };


  /*
   * Return true if the value of this Decimal is positive, otherwise return false.
   *
   */
  P.isPositive = P.ispos = function () {
    return this.s > 0;
  };


  /*
   * Return true if the value of this Decimal is 0, otherwise return false.
   *
   */
  P.isZero = function () {
    return this.s === 0;
  };


  /*
   * Return true if the value of this Decimal is less than `y`, otherwise return false.
   *
   */
  P.lessThan = P.lt = function (y) {
    return this.cmp(y) < 0;
  };


  /*
   * Return true if the value of this Decimal is less than or equal to `y`, otherwise return false.
   *
   */
  P.lessThanOrEqualTo = P.lte = function (y) {
    return this.cmp(y) < 1;
  };


  /*
   * Return the logarithm of the value of this Decimal to the specified base, truncated to
   * `precision` significant digits.
   *
   * If no base is specified, return log[10](x).
   *
   * log[base](x) = ln(x) / ln(base)
   *
   * The maximum error of the result is 1 ulp (unit in the last place).
   *
   * [base] {number|string|Decimal} The base of the logarithm.
   *
   */
  P.logarithm = P.log = function (base) {
    var r,
      x = this,
      Ctor = x.constructor,
      pr = Ctor.precision,
      wpr = pr + 5;

    // Default base is 10.
    if (base === void 0) {
      base = new Ctor(10);
    } else {
      base = new Ctor(base);

      // log[-b](x) = NaN
      // log[0](x)  = NaN
      // log[1](x)  = NaN
      if (base.s < 1 || base.eq(ONE)) throw Error(decimalError + 'NaN');
    }

    // log[b](-x) = NaN
    // log[b](0) = -Infinity
    if (x.s < 1) throw Error(decimalError + (x.s ? 'NaN' : '-Infinity'));

    // log[b](1) = 0
    if (x.eq(ONE)) return new Ctor(0);

    external = false;
    r = divide(ln(x, wpr), ln(base, wpr), wpr);
    external = true;

    return round(r, pr);
  };


  /*
   * Return a new Decimal whose value is the value of this Decimal minus `y`, truncated to
   * `precision` significant digits.
   *
   */
  P.minus = P.sub = function (y) {
    var x = this;
    y = new x.constructor(y);
    return x.s == y.s ? subtract(x, y) : add(x, (y.s = -y.s, y));
  };


  /*
   * Return a new Decimal whose value is the value of this Decimal modulo `y`, truncated to
   * `precision` significant digits.
   *
   */
  P.modulo = P.mod = function (y) {
    var q,
      x = this,
      Ctor = x.constructor,
      pr = Ctor.precision;

    y = new Ctor(y);

    // x % 0 = NaN
    if (!y.s) throw Error(decimalError + 'NaN');

    // Return x if x is 0.
    if (!x.s) return round(new Ctor(x), pr);

    // Prevent rounding of intermediate calculations.
    external = false;
    q = divide(x, y, 0, 1).times(y);
    external = true;

    return x.minus(q);
  };


  /*
   * Return a new Decimal whose value is the natural exponential of the value of this Decimal,
   * i.e. the base e raised to the power the value of this Decimal, truncated to `precision`
   * significant digits.
   *
   */
  P.naturalExponential = P.exp = function () {
    return exp(this);
  };


  /*
   * Return a new Decimal whose value is the natural logarithm of the value of this Decimal,
   * truncated to `precision` significant digits.
   *
   */
  P.naturalLogarithm = P.ln = function () {
    return ln(this);
  };


  /*
   * Return a new Decimal whose value is the value of this Decimal negated, i.e. as if multiplied by
   * -1.
   *
   */
  P.negated = P.neg = function () {
    var x = new this.constructor(this);
    x.s = -x.s || 0;
    return x;
  };


  /*
   * Return a new Decimal whose value is the value of this Decimal plus `y`, truncated to
   * `precision` significant digits.
   *
   */
  P.plus = P.add = function (y) {
    var x = this;
    y = new x.constructor(y);
    return x.s == y.s ? add(x, y) : subtract(x, (y.s = -y.s, y));
  };


  /*
   * Return the number of significant digits of the value of this Decimal.
   *
   * [z] {boolean|number} Whether to count integer-part trailing zeros: true, false, 1 or 0.
   *
   */
  P.precision = P.sd = function (z) {
    var e, sd, w,
      x = this;

    if (z !== void 0 && z !== !!z && z !== 1 && z !== 0) throw Error(invalidArgument + z);

    e = getBase10Exponent(x) + 1;
    w = x.d.length - 1;
    sd = w * LOG_BASE + 1;
    w = x.d[w];

    // If non-zero...
    if (w) {

      // Subtract the number of trailing zeros of the last word.
      for (; w % 10 == 0; w /= 10) sd--;

      // Add the number of digits of the first word.
      for (w = x.d[0]; w >= 10; w /= 10) sd++;
    }

    return z && e > sd ? e : sd;
  };


  /*
   * Return a new Decimal whose value is the square root of this Decimal, truncated to `precision`
   * significant digits.
   *
   */
  P.squareRoot = P.sqrt = function () {
    var e, n, pr, r, s, t, wpr,
      x = this,
      Ctor = x.constructor;

    // Negative or zero?
    if (x.s < 1) {
      if (!x.s) return new Ctor(0);

      // sqrt(-x) = NaN
      throw Error(decimalError + 'NaN');
    }

    e = getBase10Exponent(x);
    external = false;

    // Initial estimate.
    s = Math.sqrt(+x);

    // Math.sqrt underflow/overflow?
    // Pass x to Math.sqrt as integer, then adjust the exponent of the result.
    if (s == 0 || s == 1 / 0) {
      n = digitsToString(x.d);
      if ((n.length + e) % 2 == 0) n += '0';
      s = Math.sqrt(n);
      e = mathfloor((e + 1) / 2) - (e < 0 || e % 2);

      if (s == 1 / 0) {
        n = '5e' + e;
      } else {
        n = s.toExponential();
        n = n.slice(0, n.indexOf('e') + 1) + e;
      }

      r = new Ctor(n);
    } else {
      r = new Ctor(s.toString());
    }

    pr = Ctor.precision;
    s = wpr = pr + 3;

    // Newton-Raphson iteration.
    for (;;) {
      t = r;
      r = t.plus(divide(x, t, wpr + 2)).times(0.5);

      if (digitsToString(t.d).slice(0, wpr) === (n = digitsToString(r.d)).slice(0, wpr)) {
        n = n.slice(wpr - 3, wpr + 1);

        // The 4th rounding digit may be in error by -1 so if the 4 rounding digits are 9999 or
        // 4999, i.e. approaching a rounding boundary, continue the iteration.
        if (s == wpr && n == '4999') {

          // On the first iteration only, check to see if rounding up gives the exact result as the
          // nines may infinitely repeat.
          round(t, pr + 1, 0);

          if (t.times(t).eq(x)) {
            r = t;
            break;
          }
        } else if (n != '9999') {
          break;
        }

        wpr += 4;
      }
    }

    external = true;

    return round(r, pr);
  };


  /*
   * Return a new Decimal whose value is the value of this Decimal times `y`, truncated to
   * `precision` significant digits.
   *
   */
  P.times = P.mul = function (y) {
    var carry, e, i, k, r, rL, t, xdL, ydL,
      x = this,
      Ctor = x.constructor,
      xd = x.d,
      yd = (y = new Ctor(y)).d;

    // Return 0 if either is 0.
    if (!x.s || !y.s) return new Ctor(0);

    y.s *= x.s;
    e = x.e + y.e;
    xdL = xd.length;
    ydL = yd.length;

    // Ensure xd points to the longer array.
    if (xdL < ydL) {
      r = xd;
      xd = yd;
      yd = r;
      rL = xdL;
      xdL = ydL;
      ydL = rL;
    }

    // Initialise the result array with zeros.
    r = [];
    rL = xdL + ydL;
    for (i = rL; i--;) r.push(0);

    // Multiply!
    for (i = ydL; --i >= 0;) {
      carry = 0;
      for (k = xdL + i; k > i;) {
        t = r[k] + yd[i] * xd[k - i - 1] + carry;
        r[k--] = t % BASE | 0;
        carry = t / BASE | 0;
      }

      r[k] = (r[k] + carry) % BASE | 0;
    }

    // Remove trailing zeros.
    for (; !r[--rL];) r.pop();

    if (carry) ++e;
    else r.shift();

    y.d = r;
    y.e = e;

    return external ? round(y, Ctor.precision) : y;
  };


  /*
   * Return a new Decimal whose value is the value of this Decimal rounded to a maximum of `dp`
   * decimal places using rounding mode `rm` or `rounding` if `rm` is omitted.
   *
   * If `dp` is omitted, return a new Decimal whose value is the value of this Decimal.
   *
   * [dp] {number} Decimal places. Integer, 0 to MAX_DIGITS inclusive.
   * [rm] {number} Rounding mode. Integer, 0 to 8 inclusive.
   *
   */
  P.toDecimalPlaces = P.todp = function (dp, rm) {
    var x = this,
      Ctor = x.constructor;

    x = new Ctor(x);
    if (dp === void 0) return x;

    checkInt32(dp, 0, MAX_DIGITS);

    if (rm === void 0) rm = Ctor.rounding;
    else checkInt32(rm, 0, 8);

    return round(x, dp + getBase10Exponent(x) + 1, rm);
  };


  /*
   * Return a string representing the value of this Decimal in exponential notation rounded to
   * `dp` fixed decimal places using rounding mode `rounding`.
   *
   * [dp] {number} Decimal places. Integer, 0 to MAX_DIGITS inclusive.
   * [rm] {number} Rounding mode. Integer, 0 to 8 inclusive.
   *
   */
  P.toExponential = function (dp, rm) {
    var str,
      x = this,
      Ctor = x.constructor;

    if (dp === void 0) {
      str = toString(x, true);
    } else {
      checkInt32(dp, 0, MAX_DIGITS);

      if (rm === void 0) rm = Ctor.rounding;
      else checkInt32(rm, 0, 8);

      x = round(new Ctor(x), dp + 1, rm);
      str = toString(x, true, dp + 1);
    }

    return str;
  };


  /*
   * Return a string representing the value of this Decimal in normal (fixed-point) notation to
   * `dp` fixed decimal places and rounded using rounding mode `rm` or `rounding` if `rm` is
   * omitted.
   *
   * As with JavaScript numbers, (-0).toFixed(0) is '0', but e.g. (-0.00001).toFixed(0) is '-0'.
   *
   * [dp] {number} Decimal places. Integer, 0 to MAX_DIGITS inclusive.
   * [rm] {number} Rounding mode. Integer, 0 to 8 inclusive.
   *
   * (-0).toFixed(0) is '0', but (-0.1).toFixed(0) is '-0'.
   * (-0).toFixed(1) is '0.0', but (-0.01).toFixed(1) is '-0.0'.
   * (-0).toFixed(3) is '0.000'.
   * (-0.5).toFixed(0) is '-0'.
   *
   */
  P.toFixed = function (dp, rm) {
    var str, y,
      x = this,
      Ctor = x.constructor;

    if (dp === void 0) return toString(x);

    checkInt32(dp, 0, MAX_DIGITS);

    if (rm === void 0) rm = Ctor.rounding;
    else checkInt32(rm, 0, 8);

    y = round(new Ctor(x), dp + getBase10Exponent(x) + 1, rm);
    str = toString(y.abs(), false, dp + getBase10Exponent(y) + 1);

    // To determine whether to add the minus sign look at the value before it was rounded,
    // i.e. look at `x` rather than `y`.
    return x.isneg() && !x.isZero() ? '-' + str : str;
  };


  /*
   * Return a new Decimal whose value is the value of this Decimal rounded to a whole number using
   * rounding mode `rounding`.
   *
   */
  P.toInteger = P.toint = function () {
    var x = this,
      Ctor = x.constructor;
    return round(new Ctor(x), getBase10Exponent(x) + 1, Ctor.rounding);
  };


  /*
   * Return the value of this Decimal converted to a number primitive.
   *
   */
  P.toNumber = function () {
    return +this;
  };


  /*
   * Return a new Decimal whose value is the value of this Decimal raised to the power `y`,
   * truncated to `precision` significant digits.
   *
   * For non-integer or very large exponents pow(x, y) is calculated using
   *
   *   x^y = exp(y*ln(x))
   *
   * The maximum error is 1 ulp (unit in last place).
   *
   * y {number|string|Decimal} The power to which to raise this Decimal.
   *
   */
  P.toPower = P.pow = function (y) {
    var e, k, pr, r, sign, yIsInt,
      x = this,
      Ctor = x.constructor,
      guard = 12,
      yn = +(y = new Ctor(y));

    // pow(x, 0) = 1
    if (!y.s) return new Ctor(ONE);

    x = new Ctor(x);

    // pow(0, y > 0) = 0
    // pow(0, y < 0) = Infinity
    if (!x.s) {
      if (y.s < 1) throw Error(decimalError + 'Infinity');
      return x;
    }

    // pow(1, y) = 1
    if (x.eq(ONE)) return x;

    pr = Ctor.precision;

    // pow(x, 1) = x
    if (y.eq(ONE)) return round(x, pr);

    e = y.e;
    k = y.d.length - 1;
    yIsInt = e >= k;
    sign = x.s;

    if (!yIsInt) {

      // pow(x < 0, y non-integer) = NaN
      if (sign < 0) throw Error(decimalError + 'NaN');

    // If y is a small integer use the 'exponentiation by squaring' algorithm.
    } else if ((k = yn < 0 ? -yn : yn) <= MAX_SAFE_INTEGER) {
      r = new Ctor(ONE);

      // Max k of 9007199254740991 takes 53 loop iterations.
      // Maximum digits array length; leaves [28, 34] guard digits.
      e = Math.ceil(pr / LOG_BASE + 4);

      external = false;

      for (;;) {
        if (k % 2) {
          r = r.times(x);
          truncate(r.d, e);
        }

        k = mathfloor(k / 2);
        if (k === 0) break;

        x = x.times(x);
        truncate(x.d, e);
      }

      external = true;

      return y.s < 0 ? new Ctor(ONE).div(r) : round(r, pr);
    }

    // Result is negative if x is negative and the last digit of integer y is odd.
    sign = sign < 0 && y.d[Math.max(e, k)] & 1 ? -1 : 1;

    x.s = 1;
    external = false;
    r = y.times(ln(x, pr + guard));
    external = true;
    r = exp(r);
    r.s = sign;

    return r;
  };


  /*
   * Return a string representing the value of this Decimal rounded to `sd` significant digits
   * using rounding mode `rounding`.
   *
   * Return exponential notation if `sd` is less than the number of digits necessary to represent
   * the integer part of the value in normal notation.
   *
   * [sd] {number} Significant digits. Integer, 1 to MAX_DIGITS inclusive.
   * [rm] {number} Rounding mode. Integer, 0 to 8 inclusive.
   *
   */
  P.toPrecision = function (sd, rm) {
    var e, str,
      x = this,
      Ctor = x.constructor;

    if (sd === void 0) {
      e = getBase10Exponent(x);
      str = toString(x, e <= Ctor.toExpNeg || e >= Ctor.toExpPos);
    } else {
      checkInt32(sd, 1, MAX_DIGITS);

      if (rm === void 0) rm = Ctor.rounding;
      else checkInt32(rm, 0, 8);

      x = round(new Ctor(x), sd, rm);
      e = getBase10Exponent(x);
      str = toString(x, sd <= e || e <= Ctor.toExpNeg, sd);
    }

    return str;
  };


  /*
   * Return a new Decimal whose value is the value of this Decimal rounded to a maximum of `sd`
   * significant digits using rounding mode `rm`, or to `precision` and `rounding` respectively if
   * omitted.
   *
   * [sd] {number} Significant digits. Integer, 1 to MAX_DIGITS inclusive.
   * [rm] {number} Rounding mode. Integer, 0 to 8 inclusive.
   *
   */
  P.toSignificantDigits = P.tosd = function (sd, rm) {
    var x = this,
      Ctor = x.constructor;

    if (sd === void 0) {
      sd = Ctor.precision;
      rm = Ctor.rounding;
    } else {
      checkInt32(sd, 1, MAX_DIGITS);

      if (rm === void 0) rm = Ctor.rounding;
      else checkInt32(rm, 0, 8);
    }

    return round(new Ctor(x), sd, rm);
  };


  /*
   * Return a string representing the value of this Decimal.
   *
   * Return exponential notation if this Decimal has a positive exponent equal to or greater than
   * `toExpPos`, or a negative exponent equal to or less than `toExpNeg`.
   *
   */
  P.toString = P.valueOf = P.val = P.toJSON = function () {
    var x = this,
      e = getBase10Exponent(x),
      Ctor = x.constructor;

    return toString(x, e <= Ctor.toExpNeg || e >= Ctor.toExpPos);
  };


  // Helper functions for Decimal.prototype (P) and/or Decimal methods, and their callers.


  /*
   *  add                 P.minus, P.plus
   *  checkInt32          P.todp, P.toExponential, P.toFixed, P.toPrecision, P.tosd
   *  digitsToString      P.log, P.sqrt, P.pow, toString, exp, ln
   *  divide              P.div, P.idiv, P.log, P.mod, P.sqrt, exp, ln
   *  exp                 P.exp, P.pow
   *  getBase10Exponent   P.exponent, P.sd, P.toint, P.sqrt, P.todp, P.toFixed, P.toPrecision,
   *                      P.toString, divide, round, toString, exp, ln
   *  getLn10             P.log, ln
   *  getZeroString       digitsToString, toString
   *  ln                  P.log, P.ln, P.pow, exp
   *  parseDecimal        Decimal
   *  round               P.abs, P.idiv, P.log, P.minus, P.mod, P.neg, P.plus, P.toint, P.sqrt,
   *                      P.times, P.todp, P.toExponential, P.toFixed, P.pow, P.toPrecision, P.tosd,
   *                      divide, getLn10, exp, ln
   *  subtract            P.minus, P.plus
   *  toString            P.toExponential, P.toFixed, P.toPrecision, P.toString, P.valueOf
   *  truncate            P.pow
   *
   *  Throws:             P.log, P.mod, P.sd, P.sqrt, P.pow,  checkInt32, divide, round,
   *                      getLn10, exp, ln, parseDecimal, Decimal, config
   */


  function add(x, y) {
    var carry, d, e, i, k, len, xd, yd,
      Ctor = x.constructor,
      pr = Ctor.precision;

    // If either is zero...
    if (!x.s || !y.s) {

      // Return x if y is zero.
      // Return y if y is non-zero.
      if (!y.s) y = new Ctor(x);
      return external ? round(y, pr) : y;
    }

    xd = x.d;
    yd = y.d;

    // x and y are finite, non-zero numbers with the same sign.

    k = x.e;
    e = y.e;
    xd = xd.slice();
    i = k - e;

    // If base 1e7 exponents differ...
    if (i) {
      if (i < 0) {
        d = xd;
        i = -i;
        len = yd.length;
      } else {
        d = yd;
        e = k;
        len = xd.length;
      }

      // Limit number of zeros prepended to max(ceil(pr / LOG_BASE), len) + 1.
      k = Math.ceil(pr / LOG_BASE);
      len = k > len ? k + 1 : len + 1;

      if (i > len) {
        i = len;
        d.length = 1;
      }

      // Prepend zeros to equalise exponents. Note: Faster to use reverse then do unshifts.
      d.reverse();
      for (; i--;) d.push(0);
      d.reverse();
    }

    len = xd.length;
    i = yd.length;

    // If yd is longer than xd, swap xd and yd so xd points to the longer array.
    if (len - i < 0) {
      i = len;
      d = yd;
      yd = xd;
      xd = d;
    }

    // Only start adding at yd.length - 1 as the further digits of xd can be left as they are.
    for (carry = 0; i;) {
      carry = (xd[--i] = xd[i] + yd[i] + carry) / BASE | 0;
      xd[i] %= BASE;
    }

    if (carry) {
      xd.unshift(carry);
      ++e;
    }

    // Remove trailing zeros.
    // No need to check for zero, as +x + +y != 0 && -x + -y != 0
    for (len = xd.length; xd[--len] == 0;) xd.pop();

    y.d = xd;
    y.e = e;

    return external ? round(y, pr) : y;
  }


  function checkInt32(i, min, max) {
    if (i !== ~~i || i < min || i > max) {
      throw Error(invalidArgument + i);
    }
  }


  function digitsToString(d) {
    var i, k, ws,
      indexOfLastWord = d.length - 1,
      str = '',
      w = d[0];

    if (indexOfLastWord > 0) {
      str += w;
      for (i = 1; i < indexOfLastWord; i++) {
        ws = d[i] + '';
        k = LOG_BASE - ws.length;
        if (k) str += getZeroString(k);
        str += ws;
      }

      w = d[i];
      ws = w + '';
      k = LOG_BASE - ws.length;
      if (k) str += getZeroString(k);
    } else if (w === 0) {
      return '0';
    }

    // Remove trailing zeros of last w.
    for (; w % 10 === 0;) w /= 10;

    return str + w;
  }


  var divide = (function () {

    // Assumes non-zero x and k, and hence non-zero result.
    function multiplyInteger(x, k) {
      var temp,
        carry = 0,
        i = x.length;

      for (x = x.slice(); i--;) {
        temp = x[i] * k + carry;
        x[i] = temp % BASE | 0;
        carry = temp / BASE | 0;
      }

      if (carry) x.unshift(carry);

      return x;
    }

    function compare(a, b, aL, bL) {
      var i, r;

      if (aL != bL) {
        r = aL > bL ? 1 : -1;
      } else {
        for (i = r = 0; i < aL; i++) {
          if (a[i] != b[i]) {
            r = a[i] > b[i] ? 1 : -1;
            break;
          }
        }
      }

      return r;
    }

    function subtract(a, b, aL) {
      var i = 0;

      // Subtract b from a.
      for (; aL--;) {
        a[aL] -= i;
        i = a[aL] < b[aL] ? 1 : 0;
        a[aL] = i * BASE + a[aL] - b[aL];
      }

      // Remove leading zeros.
      for (; !a[0] && a.length > 1;) a.shift();
    }

    return function (x, y, pr, dp) {
      var cmp, e, i, k, prod, prodL, q, qd, rem, remL, rem0, sd, t, xi, xL, yd0, yL, yz,
        Ctor = x.constructor,
        sign = x.s == y.s ? 1 : -1,
        xd = x.d,
        yd = y.d;

      // Either 0?
      if (!x.s) return new Ctor(x);
      if (!y.s) throw Error(decimalError + 'Division by zero');

      e = x.e - y.e;
      yL = yd.length;
      xL = xd.length;
      q = new Ctor(sign);
      qd = q.d = [];

      // Result exponent may be one less than e.
      for (i = 0; yd[i] == (xd[i] || 0); ) ++i;
      if (yd[i] > (xd[i] || 0)) --e;

      if (pr == null) {
        sd = pr = Ctor.precision;
      } else if (dp) {
        sd = pr + (getBase10Exponent(x) - getBase10Exponent(y)) + 1;
      } else {
        sd = pr;
      }

      if (sd < 0) return new Ctor(0);

      // Convert precision in number of base 10 digits to base 1e7 digits.
      sd = sd / LOG_BASE + 2 | 0;
      i = 0;

      // divisor < 1e7
      if (yL == 1) {
        k = 0;
        yd = yd[0];
        sd++;

        // k is the carry.
        for (; (i < xL || k) && sd--; i++) {
          t = k * BASE + (xd[i] || 0);
          qd[i] = t / yd | 0;
          k = t % yd | 0;
        }

      // divisor >= 1e7
      } else {

        // Normalise xd and yd so highest order digit of yd is >= BASE/2
        k = BASE / (yd[0] + 1) | 0;

        if (k > 1) {
          yd = multiplyInteger(yd, k);
          xd = multiplyInteger(xd, k);
          yL = yd.length;
          xL = xd.length;
        }

        xi = yL;
        rem = xd.slice(0, yL);
        remL = rem.length;

        // Add zeros to make remainder as long as divisor.
        for (; remL < yL;) rem[remL++] = 0;

        yz = yd.slice();
        yz.unshift(0);
        yd0 = yd[0];

        if (yd[1] >= BASE / 2) ++yd0;

        do {
          k = 0;

          // Compare divisor and remainder.
          cmp = compare(yd, rem, yL, remL);

          // If divisor < remainder.
          if (cmp < 0) {

            // Calculate trial digit, k.
            rem0 = rem[0];
            if (yL != remL) rem0 = rem0 * BASE + (rem[1] || 0);

            // k will be how many times the divisor goes into the current remainder.
            k = rem0 / yd0 | 0;

            //  Algorithm:
            //  1. product = divisor * trial digit (k)
            //  2. if product > remainder: product -= divisor, k--
            //  3. remainder -= product
            //  4. if product was < remainder at 2:
            //    5. compare new remainder and divisor
            //    6. If remainder > divisor: remainder -= divisor, k++

            if (k > 1) {
              if (k >= BASE) k = BASE - 1;

              // product = divisor * trial digit.
              prod = multiplyInteger(yd, k);
              prodL = prod.length;
              remL = rem.length;

              // Compare product and remainder.
              cmp = compare(prod, rem, prodL, remL);

              // product > remainder.
              if (cmp == 1) {
                k--;

                // Subtract divisor from product.
                subtract(prod, yL < prodL ? yz : yd, prodL);
              }
            } else {

              // cmp is -1.
              // If k is 0, there is no need to compare yd and rem again below, so change cmp to 1
              // to avoid it. If k is 1 there is a need to compare yd and rem again below.
              if (k == 0) cmp = k = 1;
              prod = yd.slice();
            }

            prodL = prod.length;
            if (prodL < remL) prod.unshift(0);

            // Subtract product from remainder.
            subtract(rem, prod, remL);

            // If product was < previous remainder.
            if (cmp == -1) {
              remL = rem.length;

              // Compare divisor and new remainder.
              cmp = compare(yd, rem, yL, remL);

              // If divisor < new remainder, subtract divisor from remainder.
              if (cmp < 1) {
                k++;

                // Subtract divisor from remainder.
                subtract(rem, yL < remL ? yz : yd, remL);
              }
            }

            remL = rem.length;
          } else if (cmp === 0) {
            k++;
            rem = [0];
          }    // if cmp === 1, k will be 0

          // Add the next digit, k, to the result array.
          qd[i++] = k;

          // Update the remainder.
          if (cmp && rem[0]) {
            rem[remL++] = xd[xi] || 0;
          } else {
            rem = [xd[xi]];
            remL = 1;
          }

        } while ((xi++ < xL || rem[0] !== void 0) && sd--);
      }

      // Leading zero?
      if (!qd[0]) qd.shift();

      q.e = e;

      return round(q, dp ? pr + getBase10Exponent(q) + 1 : pr);
    };
  })();


  /*
   * Return a new Decimal whose value is the natural exponential of `x` truncated to `sd`
   * significant digits.
   *
   * Taylor/Maclaurin series.
   *
   * exp(x) = x^0/0! + x^1/1! + x^2/2! + x^3/3! + ...
   *
   * Argument reduction:
   *   Repeat x = x / 32, k += 5, until |x| < 0.1
   *   exp(x) = exp(x / 2^k)^(2^k)
   *
   * Previously, the argument was initially reduced by
   * exp(x) = exp(r) * 10^k  where r = x - k * ln10, k = floor(x / ln10)
   * to first put r in the range [0, ln10], before dividing by 32 until |x| < 0.1, but this was
   * found to be slower than just dividing repeatedly by 32 as above.
   *
   * (Math object integer min/max: Math.exp(709) = 8.2e+307, Math.exp(-745) = 5e-324)
   *
   *  exp(x) is non-terminating for any finite, non-zero x.
   *
   */
  function exp(x, sd) {
    var denominator, guard, pow, sum, t, wpr,
      i = 0,
      k = 0,
      Ctor = x.constructor,
      pr = Ctor.precision;

    if (getBase10Exponent(x) > 16) throw Error(exponentOutOfRange + getBase10Exponent(x));

    // exp(0) = 1
    if (!x.s) return new Ctor(ONE);

    if (sd == null) {
      external = false;
      wpr = pr;
    } else {
      wpr = sd;
    }

    t = new Ctor(0.03125);

    while (x.abs().gte(0.1)) {
      x = x.times(t);    // x = x / 2^5
      k += 5;
    }

    // Estimate the precision increase necessary to ensure the first 4 rounding digits are correct.
    guard = Math.log(mathpow(2, k)) / Math.LN10 * 2 + 5 | 0;
    wpr += guard;
    denominator = pow = sum = new Ctor(ONE);
    Ctor.precision = wpr;

    for (;;) {
      pow = round(pow.times(x), wpr);
      denominator = denominator.times(++i);
      t = sum.plus(divide(pow, denominator, wpr));

      if (digitsToString(t.d).slice(0, wpr) === digitsToString(sum.d).slice(0, wpr)) {
        while (k--) sum = round(sum.times(sum), wpr);
        Ctor.precision = pr;
        return sd == null ? (external = true, round(sum, pr)) : sum;
      }

      sum = t;
    }
  }


  // Calculate the base 10 exponent from the base 1e7 exponent.
  function getBase10Exponent(x) {
    var e = x.e * LOG_BASE,
      w = x.d[0];

    // Add the number of digits of the first word of the digits array.
    for (; w >= 10; w /= 10) e++;
    return e;
  }


  function getLn10(Ctor, sd, pr) {

    if (sd > Ctor.LN10.sd()) {


      // Reset global state in case the exception is caught.
      external = true;
      if (pr) Ctor.precision = pr;
      throw Error(decimalError + 'LN10 precision limit exceeded');
    }

    return round(new Ctor(Ctor.LN10), sd);
  }


  function getZeroString(k) {
    var zs = '';
    for (; k--;) zs += '0';
    return zs;
  }


  /*
   * Return a new Decimal whose value is the natural logarithm of `x` truncated to `sd` significant
   * digits.
   *
   *  ln(n) is non-terminating (n != 1)
   *
   */
  function ln(y, sd) {
    var c, c0, denominator, e, numerator, sum, t, wpr, x2,
      n = 1,
      guard = 10,
      x = y,
      xd = x.d,
      Ctor = x.constructor,
      pr = Ctor.precision;

    // ln(-x) = NaN
    // ln(0) = -Infinity
    if (x.s < 1) throw Error(decimalError + (x.s ? 'NaN' : '-Infinity'));

    // ln(1) = 0
    if (x.eq(ONE)) return new Ctor(0);

    if (sd == null) {
      external = false;
      wpr = pr;
    } else {
      wpr = sd;
    }

    if (x.eq(10)) {
      if (sd == null) external = true;
      return getLn10(Ctor, wpr);
    }

    wpr += guard;
    Ctor.precision = wpr;
    c = digitsToString(xd);
    c0 = c.charAt(0);
    e = getBase10Exponent(x);

    if (Math.abs(e) < 1.5e15) {

      // Argument reduction.
      // The series converges faster the closer the argument is to 1, so using
      // ln(a^b) = b * ln(a),   ln(a) = ln(a^b) / b
      // multiply the argument by itself until the leading digits of the significand are 7, 8, 9,
      // 10, 11, 12 or 13, recording the number of multiplications so the sum of the series can
      // later be divided by this number, then separate out the power of 10 using
      // ln(a*10^b) = ln(a) + b*ln(10).

      // max n is 21 (gives 0.9, 1.0 or 1.1) (9e15 / 21 = 4.2e14).
      //while (c0 < 9 && c0 != 1 || c0 == 1 && c.charAt(1) > 1) {
      // max n is 6 (gives 0.7 - 1.3)
      while (c0 < 7 && c0 != 1 || c0 == 1 && c.charAt(1) > 3) {
        x = x.times(y);
        c = digitsToString(x.d);
        c0 = c.charAt(0);
        n++;
      }

      e = getBase10Exponent(x);

      if (c0 > 1) {
        x = new Ctor('0.' + c);
        e++;
      } else {
        x = new Ctor(c0 + '.' + c.slice(1));
      }
    } else {

      // The argument reduction method above may result in overflow if the argument y is a massive
      // number with exponent >= 1500000000000000 (9e15 / 6 = 1.5e15), so instead recall this
      // function using ln(x*10^e) = ln(x) + e*ln(10).
      t = getLn10(Ctor, wpr + 2, pr).times(e + '');
      x = ln(new Ctor(c0 + '.' + c.slice(1)), wpr - guard).plus(t);

      Ctor.precision = pr;
      return sd == null ? (external = true, round(x, pr)) : x;
    }

    // x is reduced to a value near 1.

    // Taylor series.
    // ln(y) = ln((1 + x)/(1 - x)) = 2(x + x^3/3 + x^5/5 + x^7/7 + ...)
    // where x = (y - 1)/(y + 1)    (|x| < 1)
    sum = numerator = x = divide(x.minus(ONE), x.plus(ONE), wpr);
    x2 = round(x.times(x), wpr);
    denominator = 3;

    for (;;) {
      numerator = round(numerator.times(x2), wpr);
      t = sum.plus(divide(numerator, new Ctor(denominator), wpr));

      if (digitsToString(t.d).slice(0, wpr) === digitsToString(sum.d).slice(0, wpr)) {
        sum = sum.times(2);

        // Reverse the argument reduction.
        if (e !== 0) sum = sum.plus(getLn10(Ctor, wpr + 2, pr).times(e + ''));
        sum = divide(sum, new Ctor(n), wpr);

        Ctor.precision = pr;
        return sd == null ? (external = true, round(sum, pr)) : sum;
      }

      sum = t;
      denominator += 2;
    }
  }


  /*
   * Parse the value of a new Decimal `x` from string `str`.
   */
  function parseDecimal(x, str) {
    var e, i, len;

    // Decimal point?
    if ((e = str.indexOf('.')) > -1) str = str.replace('.', '');

    // Exponential form?
    if ((i = str.search(/e/i)) > 0) {

      // Determine exponent.
      if (e < 0) e = i;
      e += +str.slice(i + 1);
      str = str.substring(0, i);
    } else if (e < 0) {

      // Integer.
      e = str.length;
    }

    // Determine leading zeros.
    for (i = 0; str.charCodeAt(i) === 48;) ++i;

    // Determine trailing zeros.
    for (len = str.length; str.charCodeAt(len - 1) === 48;) --len;
    str = str.slice(i, len);

    if (str) {
      len -= i;
      e = e - i - 1;
      x.e = mathfloor(e / LOG_BASE);
      x.d = [];

      // Transform base

      // e is the base 10 exponent.
      // i is where to slice str to get the first word of the digits array.
      i = (e + 1) % LOG_BASE;
      if (e < 0) i += LOG_BASE;

      if (i < len) {
        if (i) x.d.push(+str.slice(0, i));
        for (len -= LOG_BASE; i < len;) x.d.push(+str.slice(i, i += LOG_BASE));
        str = str.slice(i);
        i = LOG_BASE - str.length;
      } else {
        i -= len;
      }

      for (; i--;) str += '0';
      x.d.push(+str);

      if (external && (x.e > MAX_E || x.e < -MAX_E)) throw Error(exponentOutOfRange + e);
    } else {

      // Zero.
      x.s = 0;
      x.e = 0;
      x.d = [0];
    }

    return x;
  }


  /*
   * Round `x` to `sd` significant digits, using rounding mode `rm` if present (truncate otherwise).
   */
   function round(x, sd, rm) {
    var i, j, k, n, rd, doRound, w, xdi,
      xd = x.d;

    // rd: the rounding digit, i.e. the digit after the digit that may be rounded up.
    // w: the word of xd which contains the rounding digit, a base 1e7 number.
    // xdi: the index of w within xd.
    // n: the number of digits of w.
    // i: what would be the index of rd within w if all the numbers were 7 digits long (i.e. if
    // they had leading zeros)
    // j: if > 0, the actual index of rd within w (if < 0, rd is a leading zero).

    // Get the length of the first word of the digits array xd.
    for (n = 1, k = xd[0]; k >= 10; k /= 10) n++;
    i = sd - n;

    // Is the rounding digit in the first word of xd?
    if (i < 0) {
      i += LOG_BASE;
      j = sd;
      w = xd[xdi = 0];
    } else {
      xdi = Math.ceil((i + 1) / LOG_BASE);
      k = xd.length;
      if (xdi >= k) return x;
      w = k = xd[xdi];

      // Get the number of digits of w.
      for (n = 1; k >= 10; k /= 10) n++;

      // Get the index of rd within w.
      i %= LOG_BASE;

      // Get the index of rd within w, adjusted for leading zeros.
      // The number of leading zeros of w is given by LOG_BASE - n.
      j = i - LOG_BASE + n;
    }

    if (rm !== void 0) {
      k = mathpow(10, n - j - 1);

      // Get the rounding digit at index j of w.
      rd = w / k % 10 | 0;

      // Are there any non-zero digits after the rounding digit?
      doRound = sd < 0 || xd[xdi + 1] !== void 0 || w % k;

      // The expression `w % mathpow(10, n - j - 1)` returns all the digits of w to the right of the
      // digit at (left-to-right) index j, e.g. if w is 908714 and j is 2, the expression will give
      // 714.

      doRound = rm < 4
        ? (rd || doRound) && (rm == 0 || rm == (x.s < 0 ? 3 : 2))
        : rd > 5 || rd == 5 && (rm == 4 || doRound || rm == 6 &&

          // Check whether the digit to the left of the rounding digit is odd.
          ((i > 0 ? j > 0 ? w / mathpow(10, n - j) : 0 : xd[xdi - 1]) % 10) & 1 ||
            rm == (x.s < 0 ? 8 : 7));
    }

    if (sd < 1 || !xd[0]) {
      if (doRound) {
        k = getBase10Exponent(x);
        xd.length = 1;

        // Convert sd to decimal places.
        sd = sd - k - 1;

        // 1, 0.1, 0.01, 0.001, 0.0001 etc.
        xd[0] = mathpow(10, (LOG_BASE - sd % LOG_BASE) % LOG_BASE);
        x.e = mathfloor(-sd / LOG_BASE) || 0;
      } else {
        xd.length = 1;

        // Zero.
        xd[0] = x.e = x.s = 0;
      }

      return x;
    }

    // Remove excess digits.
    if (i == 0) {
      xd.length = xdi;
      k = 1;
      xdi--;
    } else {
      xd.length = xdi + 1;
      k = mathpow(10, LOG_BASE - i);

      // E.g. 56700 becomes 56000 if 7 is the rounding digit.
      // j > 0 means i > number of leading zeros of w.
      xd[xdi] = j > 0 ? (w / mathpow(10, n - j) % mathpow(10, j) | 0) * k : 0;
    }

    if (doRound) {
      for (;;) {

        // Is the digit to be rounded up in the first word of xd?
        if (xdi == 0) {
          if ((xd[0] += k) == BASE) {
            xd[0] = 1;
            ++x.e;
          }

          break;
        } else {
          xd[xdi] += k;
          if (xd[xdi] != BASE) break;
          xd[xdi--] = 0;
          k = 1;
        }
      }
    }

    // Remove trailing zeros.
    for (i = xd.length; xd[--i] === 0;) xd.pop();

    if (external && (x.e > MAX_E || x.e < -MAX_E)) {
      throw Error(exponentOutOfRange + getBase10Exponent(x));
    }

    return x;
  }


  function subtract(x, y) {
    var d, e, i, j, k, len, xd, xe, xLTy, yd,
      Ctor = x.constructor,
      pr = Ctor.precision;

    // Return y negated if x is zero.
    // Return x if y is zero and x is non-zero.
    if (!x.s || !y.s) {
      if (y.s) y.s = -y.s;
      else y = new Ctor(x);
      return external ? round(y, pr) : y;
    }

    xd = x.d;
    yd = y.d;

    // x and y are non-zero numbers with the same sign.

    e = y.e;
    xe = x.e;
    xd = xd.slice();
    k = xe - e;

    // If exponents differ...
    if (k) {
      xLTy = k < 0;

      if (xLTy) {
        d = xd;
        k = -k;
        len = yd.length;
      } else {
        d = yd;
        e = xe;
        len = xd.length;
      }

      // Numbers with massively different exponents would result in a very high number of zeros
      // needing to be prepended, but this can be avoided while still ensuring correct rounding by
      // limiting the number of zeros to `Math.ceil(pr / LOG_BASE) + 2`.
      i = Math.max(Math.ceil(pr / LOG_BASE), len) + 2;

      if (k > i) {
        k = i;
        d.length = 1;
      }

      // Prepend zeros to equalise exponents.
      d.reverse();
      for (i = k; i--;) d.push(0);
      d.reverse();

    // Base 1e7 exponents equal.
    } else {

      // Check digits to determine which is the bigger number.

      i = xd.length;
      len = yd.length;
      xLTy = i < len;
      if (xLTy) len = i;

      for (i = 0; i < len; i++) {
        if (xd[i] != yd[i]) {
          xLTy = xd[i] < yd[i];
          break;
        }
      }

      k = 0;
    }

    if (xLTy) {
      d = xd;
      xd = yd;
      yd = d;
      y.s = -y.s;
    }

    len = xd.length;

    // Append zeros to xd if shorter.
    // Don't add zeros to yd if shorter as subtraction only needs to start at yd length.
    for (i = yd.length - len; i > 0; --i) xd[len++] = 0;

    // Subtract yd from xd.
    for (i = yd.length; i > k;) {
      if (xd[--i] < yd[i]) {
        for (j = i; j && xd[--j] === 0;) xd[j] = BASE - 1;
        --xd[j];
        xd[i] += BASE;
      }

      xd[i] -= yd[i];
    }

    // Remove trailing zeros.
    for (; xd[--len] === 0;) xd.pop();

    // Remove leading zeros and adjust exponent accordingly.
    for (; xd[0] === 0; xd.shift()) --e;

    // Zero?
    if (!xd[0]) return new Ctor(0);

    y.d = xd;
    y.e = e;

    //return external && xd.length >= pr / LOG_BASE ? round(y, pr) : y;
    return external ? round(y, pr) : y;
  }


  function toString(x, isExp, sd) {
    var k,
      e = getBase10Exponent(x),
      str = digitsToString(x.d),
      len = str.length;

    if (isExp) {
      if (sd && (k = sd - len) > 0) {
        str = str.charAt(0) + '.' + str.slice(1) + getZeroString(k);
      } else if (len > 1) {
        str = str.charAt(0) + '.' + str.slice(1);
      }

      str = str + (e < 0 ? 'e' : 'e+') + e;
    } else if (e < 0) {
      str = '0.' + getZeroString(-e - 1) + str;
      if (sd && (k = sd - len) > 0) str += getZeroString(k);
    } else if (e >= len) {
      str += getZeroString(e + 1 - len);
      if (sd && (k = sd - e - 1) > 0) str = str + '.' + getZeroString(k);
    } else {
      if ((k = e + 1) < len) str = str.slice(0, k) + '.' + str.slice(k);
      if (sd && (k = sd - len) > 0) {
        if (e + 1 === len) str += '.';
        str += getZeroString(k);
      }
    }

    return x.s < 0 ? '-' + str : str;
  }


  // Does not strip trailing zeros.
  function truncate(arr, len) {
    if (arr.length > len) {
      arr.length = len;
      return true;
    }
  }


  // Decimal methods


  /*
   *  clone
   *  config/set
   */


  /*
   * Create and return a Decimal constructor with the same configuration properties as this Decimal
   * constructor.
   *
   */
  function clone(obj) {
    var i, p, ps;

    /*
     * The Decimal constructor and exported function.
     * Return a new Decimal instance.
     *
     * value {number|string|Decimal} A numeric value.
     *
     */
    function Decimal(value) {
      var x = this;

      // Decimal called without new.
      if (!(x instanceof Decimal)) return new Decimal(value);

      // Retain a reference to this Decimal constructor, and shadow Decimal.prototype.constructor
      // which points to Object.
      x.constructor = Decimal;

      // Duplicate.
      if (value instanceof Decimal) {
        x.s = value.s;
        x.e = value.e;
        x.d = (value = value.d) ? value.slice() : value;
        return;
      }

      if (typeof value === 'number') {

        // Reject Infinity/NaN.
        if (value * 0 !== 0) {
          throw Error(invalidArgument + value);
        }

        if (value > 0) {
          x.s = 1;
        } else if (value < 0) {
          value = -value;
          x.s = -1;
        } else {
          x.s = 0;
          x.e = 0;
          x.d = [0];
          return;
        }

        // Fast path for small integers.
        if (value === ~~value && value < 1e7) {
          x.e = 0;
          x.d = [value];
          return;
        }

        return parseDecimal(x, value.toString());
      } else if (typeof value !== 'string') {
        throw Error(invalidArgument + value);
      }

      // Minus sign?
      if (value.charCodeAt(0) === 45) {
        value = value.slice(1);
        x.s = -1;
      } else {
        x.s = 1;
      }

      if (isDecimal.test(value)) parseDecimal(x, value);
      else throw Error(invalidArgument + value);
    }

    Decimal.prototype = P;

    Decimal.ROUND_UP = 0;
    Decimal.ROUND_DOWN = 1;
    Decimal.ROUND_CEIL = 2;
    Decimal.ROUND_FLOOR = 3;
    Decimal.ROUND_HALF_UP = 4;
    Decimal.ROUND_HALF_DOWN = 5;
    Decimal.ROUND_HALF_EVEN = 6;
    Decimal.ROUND_HALF_CEIL = 7;
    Decimal.ROUND_HALF_FLOOR = 8;

    Decimal.clone = clone;
    Decimal.config = Decimal.set = config;

    if (obj === void 0) obj = {};
    if (obj) {
      ps = ['precision', 'rounding', 'toExpNeg', 'toExpPos', 'LN10'];
      for (i = 0; i < ps.length;) if (!obj.hasOwnProperty(p = ps[i++])) obj[p] = this[p];
    }

    Decimal.config(obj);

    return Decimal;
  }


  /*
   * Configure global settings for a Decimal constructor.
   *
   * `obj` is an object with one or more of the following properties,
   *
   *   precision  {number}
   *   rounding   {number}
   *   toExpNeg   {number}
   *   toExpPos   {number}
   *
   * E.g. Decimal.config({ precision: 20, rounding: 4 })
   *
   */
  function config(obj) {
    if (!obj || typeof obj !== 'object') {
      throw Error(decimalError + 'Object expected');
    }
    var i, p, v,
      ps = [
        'precision', 1, MAX_DIGITS,
        'rounding', 0, 8,
        'toExpNeg', -1 / 0, 0,
        'toExpPos', 0, 1 / 0
      ];

    for (i = 0; i < ps.length; i += 3) {
      if ((v = obj[p = ps[i]]) !== void 0) {
        if (mathfloor(v) === v && v >= ps[i + 1] && v <= ps[i + 2]) this[p] = v;
        else throw Error(invalidArgument + p + ': ' + v);
      }
    }

    if ((v = obj[p = 'LN10']) !== void 0) {
        if (v == Math.LN10) this[p] = new this(v);
        else throw Error(invalidArgument + p + ': ' + v);
    }

    return this;
  }


  // Create and configure initial Decimal constructor.
  Decimal = clone(Decimal);

  Decimal['default'] = Decimal.Decimal = Decimal;

  // Internal constant.
  ONE = new Decimal(1);


  // Export.
  return Decimal;
})();


















const currencyStrings = {
  bigInt,
  Decimal,
  Num: function (num) { 
    if (typeof num == 'string') return bigInt(num.replace(/\"/g, '').replace(/\'/g, ''));
    else return bigInt(num);
  },
  no_e: function (x) {
    let e;
    if (Math.abs(x) < 1.0) {
      e = parseInt(x.toString().split('e-')[1]);
      if (e) {
        x *= Math.pow(10, e - 1);
        x = '0.' + (new Array(e)).join('0') + x.toString().substring(2);
      }
    }
    else {
      e = parseInt(x.toString().split('+')[1]);
      if (e > 20) {
        e -= 20;
        x /= Math.pow(10, e);
        x += (new Array(e + 1)).join('0');
      }
    }
    return x;
  },
  fixed: function (coin, n) {
    if (coin == undefined) { coin = "0.00000000"; }
    if (coin.indexOf('.') == -1) { coin = coin + '.00000000' }
    coin = (coin + '0000000000000000').split('.');
    return coin[0] + '.' + (coin[1].substr(0, n));
  },
  qsat_to_readable: function (coin, input_val) {
    if (coin == undefined) { coin = "0"; }
    let neg = false;
    if (coin[0] == '-') {
      neg = true;
      coin.slice(1);
    }
    coin = coin + '';
    while (coin.length > 16 && coin[0] == '0') { coin = coin.substr(1); }
    while (coin.length < 16) { coin = '0' + coin; }
    coin = coin.split('').reverse().join('');
    if (coin.length > 16) { coin = coin.substr(0, 16) + '.' + coin.substr(16); }
    else { coin = coin + '.0'; }
    let qsat = coin.substr(0, 8)
      .replace(/0/g, '₀')
      .replace(/1/g, '₁')
      .replace(/2/g, '₂')
      .replace(/3/g, '₃')
      .replace(/4/g, '₄')
      .replace(/5/g, '₅')
      .replace(/6/g, '₆')
      .replace(/7/g, '₇')
      .replace(/8/g, '₈')
      .replace(/9/g, '₉');
    if (!input_val) { qsat = '<b style="font-size:17px;">' + (qsat.split('').reverse().join('')) + '</b>'; }
    else { qsat = qsat.split('').reverse().join(''); }
    coin = coin.substr(8);
    coin = coin.split('').reverse().join('');
    if (neg && coin[0] !== '-') { coin = '-' + coin; }
    return coin + qsat;
  },
  sat_to_readable: function (coin) {
    if (coin == undefined) { coin = "0"; }
    let neg = false;
    if (coin[0] == '-') {
      neg = true;
      coin.slice(1);
    }
    coin = coin + '';
    coin = coin.replace(/\"/g, '').replace(/\'/g, '');
    while (coin.length > 8 && coin[0] == '0') { coin = coin.substr(1); }
    while (coin.length < 8) { coin = '0' + coin; }
    coin = coin.split('').reverse().join('');
    if (coin.length > 8) { coin = coin.substr(0, 8) + '.' + coin.substr(8); }
    else { coin = coin + '.0'; }
    coin = coin.split('').reverse().join('');
    if (neg && coin[0] !== '-') { coin = '-' + coin; }
    return coin;
  },
  qsat_to_sat: function (qsat) {
    if (qsat == undefined) { qsat = "0"; }
    let neg = false;
    if (qsat[0] == '-') {
      neg = true;
      qsat.slice(1);
    }
    qsat = qsat + '';
    qsat = qsat.replace(/\"/g, '').replace(/\'/g, ''); // todo: test - altered massivly
    qsat = (qsat.length < 9) ? ("0") : (bigInt(qsat).divide(bigInt('100000000')).toString());
    if (neg && qsat[0] !== '-') { qsat = '-' + qsat; }
    return qsat;
  },
  qsat_to_qoin: function (qsat) { // 16 decimal places
    if (qsat == undefined) { qsat = "0"; }
    let neg = false;
    if (qsat[0] == '-') {
      neg = true;
      qsat.slice(1);
    }
    qsat = qsat + '';
    while (qsat.length > 16 && qsat[0] == '0') { qsat = qsat.substr(1); }
    while (qsat.length < 16) { qsat = '0' + qsat; }
    qsat = qsat.split('').reverse().join('');
    if (qsat.length > 16) { qsat = qsat.substr(0, 16) + '.' + qsat.substr(16); }
    else { qsat = qsat + '.0'; }
    qsat = qsat.split('').reverse().join('');
    if (neg && qsat[0] !== '-') { qsat = '-' + qsat; }
    return qsat;
  },
  qsat_to_coin: function (qsat) {
    if (qsat == undefined) { qsat = "0"; }
    let neg = false;
    if (qsat[0] == '-') {
      neg = true;
      qsat.slice(1);
    }
    qsat = qsat + '';
    qsat = qsat.replace(/\"/g, '').replace(/\'/g, '').replace(/\./g, '');
    while (qsat.length > 16 && qsat[0] == '0') { qsat = qsat.substr(1); }
    while (qsat.length < 16) { qsat = '0' + qsat; }
    qsat = qsat.split('').reverse().join('');
    qsat = [qsat.substr(16), qsat.substr(0, 16)];
    if (qsat[0] == '') { qsat[0] = '0'; }
    qsat[0] = qsat[0].split('').reverse().join('');
    qsat[1] = qsat[1].split('').reverse().join('');
    qsat = qsat[0] + '.' + (qsat[1].substr(0, 8));
    if (neg && qsat[0] !== '-') { qsat = '-' + qsat; }
    return qsat;
  },
  coin_to_sat: function (coin) { // not used so far?
    if (coin == undefined) { coin = "0"; }
    let neg = false;
    if (coin[0] == '-') {
      neg = true;
      coin.slice(1);
    }
    coin = coin + '';
    coin = this.fixed(coin, 8);
    coin = coin.replace(/\"/g, '').replace(/\'/g, '');
    if (coin.indexOf('.') == -1) { coin = coin + '.0'; }
    coin = coin.split('.');
    while (coin[1].length < 8) { coin[1] = coin[1] + '0'; }
    coin = coin[0] + coin[1];
    while (coin[0] == '0') { coin = coin.substr(1); }
    if (neg && coin[0] !== '-') { coin = '-' + coin; }
    return coin.replace('\n', '');
  },
  coin_to_qsat: function (coin) { // not used so far?
    if (coin == undefined) { coin = "0"; }
    let neg = false;
    if (coin[0] == '-') {
      neg = true;
      coin.slice(1);
    }
    coin = coin + '';
    coin = this.fixed(coin, 16);
    coin = coin.replace(/\"/g, '').replace(/\'/g, '');
    if (coin.indexOf('.') == -1) { coin = coin + '.0'; }
    coin = coin.split('.');
    while (coin[1].length < 16) { coin[1] = coin[1] + '0'; }
    coin = coin[0] + coin[1];
    while (coin[0] == '0') { coin = coin.substr(1); }
    if (neg && coin[0] !== '-') { coin = '-' + coin; }
    return coin.replace('\n', '');
  },
  sat_to_coin: function (sat) {
    if (sat == undefined) { sat = "0"; }
    let neg = false;
    if (sat[0] == '-') {
      neg = true;
      sat.slice(1);
    }
    sat = sat + '';
    sat = sat.replace(/\"/g, '').replace(/\'/g, '').replace(/\./g, '');
    while (sat.length > 8 && sat[0] == '0') { sat = sat.substr(1); }
    while (sat.length < 8) { sat = '0' + sat; }
    sat = sat.split('').reverse().join('');
    sat = [sat.substr(8), sat.substr(0, 8)];
    if (sat[0] == '') { sat[0] = '0'; }
    sat[0] = sat[0].split('').reverse().join('');
    sat[1] = sat[1].split('').reverse().join('');
    sat = sat[0] + '.' + (sat[1].substr(0, 8));
    if (neg && sat[0] !== '-') { sat = '-' + sat; }
    return sat;
  },
  sat_to_qsat: function (sat) {
    if (sat == undefined) { sat = "0"; }
    let neg = false;
    if (sat[0] == '-') {
      neg = true;
      sat.slice(1);
    }
    sat = sat + '';
    sat = sat.replace(/\"/g, '').replace(/\'/g, '');
    sat = (bigInt(sat).multiply(bigInt('100000000')).toString());
    if (neg && sat[0] !== '-') { sat = '-' + sat; }
    return sat;
  },
  calc_share: function (my_balance, total, new_reward) { // used 3 times?
    if (my_balance == undefined) { my_balance = "0"; }
    if (total == undefined) { total = "0"; }
    if (new_reward == undefined) { new_reward = "0"; }
    if ([my_balance, total, new_reward].indexOf("0") !== -1) { return ["0", "0", "0"]; }
    else {
      my_balance = my_balance.replace(/\"/g, '').replace(/\'/g, '');
      total = total.replace(/\"/g, '').replace(/\'/g, '');
      new_reward = new_reward.replace(/\"/g, '').replace(/\'/g, '');
      const my_share_percent = cc.no_e(new cc.Decimal(new cc.Decimal(new cc.Decimal(my_balance).times(100)).dividedBy(total)).toFixed(16));
      if (my_share_percent == "0") { return ["0", "0", "0"]; }
      else {
        const my_reward = new cc.Decimal(new cc.Decimal(new cc.Decimal(my_share_percent).times(new_reward)).dividedBy(100)).toString().split('.')[0];
        return [my_reward, my_share_percent];
      }
    }
  },
  pct_to_share: function (percent, of_number) { // returns share
    if (percent == undefined) { percent = "0"; }
    if (of_number == undefined) { of_number = "0"; }
    if ([percent, of_number].indexOf("0") !== -1) { return "0"; }
    else {
      return new cc.Decimal(percent).times(of_number).dividedBy(100).toString().split('.')[0]; // (percent*total/100)
    }
  },
  share_to_pct: function (balance, total) {
    if (balance == undefined) { balance = "0"; }
    if (total == undefined) { total = "0"; }
    balance = balance + '';
    total = total + '';
    if (balance == "0" || total == "0") { return "0"; }
    else {
      return cc.no_e(new cc.Decimal(new cc.Decimal(new cc.Decimal(balance).times(100)).dividedBy(total)).toFixed(16)); // ((balance/total)*100)
    }
  },
  add: function (a, b) {
    if (a == undefined) { a = "0"; }
    if (b == undefined) { b = "0"; }
    a = a + '';
    b = b + '';
    a = a.replace(/\"/g, '').replace(/\'/g, '');
    b = b.replace(/\"/g, '').replace(/\'/g, '');
    return bigInt(bigInt(a).add(bigInt(b))).toString();
  },
  sub: function (a, b) {
    if (a == undefined) { a = "0"; }
    if (b == undefined) { b = "0"; }
    a = a + '';
    b = b + '';
    a = a.replace(/\"/g, '').replace(/\'/g, '');
    b = b.replace(/\"/g, '').replace(/\'/g, '');
    return bigInt(bigInt(a).minus(bigInt(b))).toString();
  }
};

// Universal export pattern
if (typeof module !== 'undefined' && module.exports) {
  module.exports = currencyStrings;
} else if (typeof window !== 'undefined') {
  window.cc = currencyStrings;
}

// loading examples:
// <script src='path/to/decimal.js-light'></script> // client side
// npm install decimal.js-light
// use { strictStrings: true } to ignore or leave blank to use external version todo: test against internal/external/naked vs old version


// Usage examples:
// const strict = cc({ strictStrings: true }); // Always uses pure-string
// const lib = cc(); // Uses decimal.js or throws clear error