/**
 * This module is based on ideas by Yozu Hida, Xiaoye S. Li and David H. Bailey
 * and others. A 2007 paper describing the concept is available at
 * http://www.jaist.ac.jp/~s1410018/papers/qd.pdf.
 *
 * This module currently only implements a small subset of their algorithms.
 */

/**
 * Remarks / Issues:
 *  - Correct propagation of infinity and NaN is not tested.
 *  - double-double operations during compile-time are broken. CTFE is
 *    explicitly disabled for the relevant functions to avoid problems.
 *  - Algorithms rely on certain setting of the FPU like rounding mode. Should
 *    be correct by default, but no checks are done.
 *  - Basic operations are implemented without control-flow. This should make
 *    vectorization straight-forward if the need ever arises.
 *  - Operations are generally implemented as
 *      (1) compute a double-precision approximation (e.g. using std.math)
 *      (2) compute one correction term (e.g. using Newton-Raphson)
 *    In principle, the second step doubles the accuracy of the result, but
 *    for some combinations of operands it does not. In practice this does not
 *    seem to matter and "more precise" algorithms would waste performance.
 */

/*
 * TODO:
 *  - toString/fromString are not as fast or accurate as they could be because
 *    they rely on repeated multiplication/division by 10.
 *  - use hardware FMA for compilers other than LDC
 *  - possible optimizations for transcendental functions
 *      - giant-step/baby-step
 *      - double precision suffices for last few terms
 *      - use exp(x) = exp(x/16)^16 to speed up convergence (check accuracy!)
 *      - logarithmic expressions for inverse hyperbolic functions
 */

module highprec.ddouble;

import std.math;
import std.traits;
import std.format;
import std.random;
import std.traits;

//debug = ddouble;

/**
 * "double double" type which is a (non-IEEE) floating point type implemented
 * as the sum of two doubles and thus has about 107 bits of effective
 * mantissa. This should be significantly faster than an actual multi-precision
 * library like MPFR. So as long as quadruple precision is not supported by
 * hardware, this is the most efficient alternative in cases where only a
 * little more than double-precision is needed.
 */
struct ddouble
{
	//////////////////////////////////////////////////////////////////////
	/// internals and some constants
	//////////////////////////////////////////////////////////////////////

	double hi;
	double lo;

	/** special values */
	enum nan = ddouble(double.nan, double.nan);
	enum infinity = ddouble(double.infinity, double.infinity);
	enum epsilon = ddouble(double.epsilon^^2, 0);

	/** mathematical constants (same list as std.math) */
	enum E          = ddouble(0x1.5bf0a8b145769p+1,  0x1.4d57ee2b1013ap-53);
	enum LOG2T      = ddouble(0x1.a934f0979a371p+1,  0x1.7f2495fb7fa6dp-53);
	enum LOG2E      = ddouble(0x1.71547652b82fep+0,  0x1.777d0ffda0d24p-56);
	enum LOG2       = ddouble(0x1.34413509f79ffp-2, -0x1.9dc1da994fd21p-59);
	enum LOG10E     = ddouble(0x1.bcb7b1526e50ep-2,  0x1.95355baaafad3p-57);
	enum LN2        = ddouble(0x1.62e42fefa39efp-1,  0x1.abc9e3b39803fp-56);
	enum LN10       = ddouble(0x1.26bb1bbb55516p+1, -0x1.f48ad494ea3e9p-53);
	enum PI         = ddouble(0x1.921fb54442d18p+1,  0x1.1a62633145c07p-53);
	enum PI_2       = ddouble(0x1.921fb54442d18p+0,  0x1.1a62633145c07p-54);
	enum PI_4       = ddouble(0x1.921fb54442d18p-1,  0x1.1a62633145c07p-55);
	enum M_1_PI     = ddouble(0x1.45f306dc9c883p-2, -0x1.6b01ec5417056p-56);
	enum M_2_PI     = ddouble(0x1.45f306dc9c883p-1, -0x1.6b01ec5417056p-55);
	enum M_2_SQRTPI = ddouble(0x1.20dd750429b6dp+0,  0x1.1ae3a914fed8p0-56);
	enum SQRT2      = ddouble(0x1.6a09e667f3bcdp+0, -0x1.bdd3413b26456p-54);
	enum SQRT1_2    = ddouble(0x1.6a09e667f3bcdp-1, -0x1.bdd3413b26456p-55);

	debug(ddouble) invariant
	{
		if(isNaN(hi) || isNaN(lo))
			return;

		// During CTFE, doubles are promoted to real for extra precision.
		// That makes double-double impossible.
		if(__ctfe)
			return;

		assert(hi + lo == hi); // this is the essence of the double-double type
	}


	//////////////////////////////////////////////////////////////////////
	/// constructors and basic casts
	//////////////////////////////////////////////////////////////////////

	private this(double hi, double lo) pure @safe nothrow
	{
		this.hi = hi;
		this.lo = lo;
	}

	/** constructor taking float/double */
	this(S)(S x) pure @safe nothrow
		if(is(Unqual!S == float) || is(Unqual!S == double))
	{
		this.hi = x;
		this.lo = 0;
	}

	/** constructor taking int/long */
	this(S)(S x) pure @safe nothrow
		if(isIntegral!S)
	{
		static if(S.sizeof <= 4)
		{
			this.hi = x;
			this.lo = 0;
		}
		else static if(S.sizeof == 8)
		{
			this.hi = x & cast(S)0xFFFF_FFFF_0000_0000_L;
			this.lo = x & cast(S)0x0000_0000_FFFF_FFFF_L;
			twoSumQuick(hi, lo, hi, lo);
		}
		else static assert(false, S.stringof);
	}

	/**
	 * Constructor taking a (decimal) string in scientific notation.
	 */
	this(string s) pure @safe
	{
		this(0,0);
		size_t k = 0;

		// sign
		bool sign = false;
		if(k < s.length && s[k] == '-')
		{
			++k;
			sign = true;
		}

		// whole part
		for(; k < s.length && '0' <= s[k] && s[k] <= '9'; ++k)
			this = 10 * this + (s[k]-'0');

		// fractional part
		if(k < s.length && s[k] == '.')
		{
			++k;
			ddouble inc = 1;
			for(; k < s.length && '0' <= s[k] && s[k] <= '9'; ++k)
			{
				inc /= 10;
				this += inc * (s[k] - '0');
			}
		}

		// exponent
		if(k < s.length && (s[k] == 'e' || s[k] == 'E'))
		{
			++k;
			bool esign = false;
			if(k < s.length && s[k] == '-')
			{
				++k;
				esign = true;
			}
			int e;
			for(; k < s.length && '0' <= s[k] && s[k] <= '9'; ++k)
				e = 10 * e + (s[k]-'0');
			if(esign)
				this *= ddouble(10)^^-e;
			else
				this *= ddouble(10)^^e;
		}

		if(k != s.length)
			throw new Exception("invalid floating point string: '"~s~"'");
		if(sign)
		{
			hi = -hi;
			lo = -lo;
		}
	}

	/**
	 * Generate a random number in [0,1).
	 */
	static ddouble urandom()
	{
		return ddouble(uniform!ulong).ldexp(-64) + ddouble(uniform!ulong).ldexp(-128);
	}

	alias random = urandom;

	/** only scientific notation is supported right now */
	void toString(scope void delegate(const(char)[]) sink, FormatSpec!char fmt) const
	{
		// hexadecimal format
		if(fmt.spec == 'a')
			return cast(void)formattedWrite(sink, "(%a, %a)", hi, lo);
		if(fmt.spec == 'A')
			return cast(void)formattedWrite(sink, "(%A, %A)", hi, lo);

		// special cases and sign
		if(isNaN(hi))
			return sink("nan");
		if(hi < 0)
			sink("-");
		if(hi == double.infinity || hi == -double.infinity)
			sink("inf");
		if(hi == 0)
			return sink("0");
		assert(isFinite(hi) && isFinite(lo));

		// split abs(this) = x * 10^e
		auto e = cast(int)std.math.log10(std.math.abs(hi));
		auto x = this.abs * (ddouble(10) ^^ -e);
		if(x < 1)
		{
			x *= 10;
			e -= 1;
		}
		else if(x >= 10)
		{
			x /= 10;
			e += 1;
		}
		assert(1 <= x && x < 10);

		// write mantissa
		enum digits = ["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"];
		int prec = fmt.precision;
		if(prec == FormatSpec!char.UNSPECIFIED)
			prec = 7; // same default as for float/double
		assert(prec > 0);
		sink(digits[cast(int)x]);
		if(prec > 1)
			sink(".");
		for(int i = 1; i < prec; ++i)
		{
			x -= cast(int)x;
			x = 10*x;
			sink(digits[cast(int)x]);
		}

		// write exponent
		if(e != 0)
		{
			sink("e");
			sink(format("%s", e));
		}
	}

	/** default formatting */
	string toString() const
	{
		return format("%s");
	}

	/** casts to builtin types */
	T opCast(T)() const pure @safe nothrow
	{
		static if(is(T == float) || is(T == double))
			return hi;
		else static if(is(T == int))
			return cast(int)hi;
		else static if(is(T == string))
			return toString();
		else static assert(false, "cast not implementd: ddouble -> "~T.stringof);
	}

	void opAssign(double x) pure @safe nothrow
	{
		hi = x;
		lo = 0;
	}


	//////////////////////////////////////////////////////////////////////
	/// arithmetic
	//////////////////////////////////////////////////////////////////////

	/** +- ddouble */
	ddouble opUnary(string op)() const pure @safe nothrow
	{
		static if(op == "+")
			return ddouble(hi, lo);
		else static if(op == "-")
			return ddouble(-hi, -lo);
		else static assert(false);
	}

	/** ddouble + double */
	ddouble opBinary(string op)(double b) const pure @safe nothrow
		if(op == "+")
	{
		double rhi, rlo;
		twoSum(hi, b, rhi, rlo);
		rlo += lo;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** ddouble - double */
	ddouble opBinary(string op)(double b) const pure @safe nothrow
		if(op == "-")
	{
		return this + (-b);
	}

	/** ddouble * double */
	ddouble opBinary(string op)(double b) const pure @safe nothrow
		if(op == "*")
	{
		double rhi, rlo;
		twoProd(hi, b, rhi, rlo);
		rlo += lo * b;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** ddouble / double */
	ddouble opBinary(string op)(double b) const pure @safe nothrow
		if(op == "/")
	{
		double rhi, rlo;
		rhi = hi / b;
		rlo = (this - ddouble(b) * rhi).hi / b;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** double + ddouble */
	ddouble opBinaryRight(string op)(double a) const pure @safe nothrow
		if(op == "+")
	{
		return this + a;
	}

	/** double - ddouble */
	ddouble opBinaryRight(string op)(double a) const pure @safe nothrow
		if(op == "-")
	{
		return (-this) + a;
	}

	/** double * ddouble */
	ddouble opBinaryRight(string op)(double a) const pure @safe nothrow
		if(op == "*")
	{
		return this * a;
	}

	/** double / ddouble */
	ddouble opBinaryRight(string op)(double a) const pure @safe nothrow
		if(op == "/")
	{
		double rhi, rlo;
		rhi = a / hi;
		rlo = (a - this * rhi).hi / hi;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** ddouble + ddouble */
	ddouble opBinary(string op)(ddouble b) const pure @safe nothrow
		if(op == "+")
	{
		double rhi, rlo;
		twoSum(hi, b.hi, rhi, rlo);
		rlo += lo + b.lo;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** ddouble - ddouble */
	ddouble opBinary(string op)(ddouble b) const pure @safe nothrow
		if(op == "-")
	{
		return this + (-b);
	}

	/** ddouble * ddouble */
	ddouble opBinary(string op)(ddouble b) const pure @safe nothrow
		if(op == "*")
	{
		double rhi, rlo;
		twoProd(hi, b.hi, rhi, rlo);
		rlo += hi * b.lo + lo * b.hi;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** ddouble / ddouble */
	ddouble opBinary(string op)(ddouble b) const pure @safe nothrow
		if(op == "/")
	{
		double rhi, rlo;
		rhi = hi / b.hi;
		rlo = (this - b * rhi).hi / b.hi;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** ddouble ^^ long */
	ddouble opBinary(string op)(long n) const pure @safe nothrow
		if(op == "^^")
	{
		if(n == 0)
			return ddouble(1);

		ddouble a = this;
		if(n < 0)
		{
			a = a.inverse;
			n = -n;
		}

		ddouble r = ddouble(1);
		for(; n != 0; n >>= 1, a = a.sqr)
			if(n & 1)
				r *= a;
		return r;
	}

	/** opOpAssign for convenience */
	ddouble opOpAssign(string op, S)(S b) pure @safe nothrow
	{
		this = this.opBinary!op(b);
		return this;
	}

	/** 1 / this */
	ddouble inverse() const pure @safe nothrow
	{
		double rhi, rlo;
		rhi = 1 / hi;
		rlo = (1 - this * rhi).hi / hi;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** absolute value */
	ddouble abs() const pure @safe nothrow
	{
		if(this < 0)
			return -this;
		else
			return this;
	}

	/** this * 2^n */
	ddouble ldexp(int n) const pure @safe nothrow
	{
		return ddouble(hi.ldexp(n), lo.ldexp(n));
	}

	/** this * this */
	ddouble sqr() const pure @safe nothrow
	{
		double rhi, rlo;
		twoSqr(hi, rhi, rlo);
		rlo += 2 * hi * lo;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** ditto */
	alias sqAbs = sqr;

	/** square root of this */
	ddouble sqrt() const pure @safe nothrow
	{
		double rhi, rlo;
		rhi = hi.sqrt;
		rlo = (this-ddouble(rhi).sqr).hi/(2*rhi);
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/* cube root of this */
	ddouble cbrt() const /*pure*/ @safe nothrow
	{
		double rhi, rlo;
		rhi = hi.cbrt;
		rlo = (this-ddouble(rhi).sqr*rhi).hi/(3*rhi);
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}


	//////////////////////////////////////////////////////////////////////
	/// exponentials and logarithms
	//////////////////////////////////////////////////////////////////////

	/** exponential function, exp(this) */
	ddouble exp() const pure @safe nothrow
	{
		// split this = n * ln(2) + a
		int n = cast(int)(this / LN2).hi.round;
		auto a = this - n * LN2;

		// remaining a is small -> Taylor
		return taylor(coeffsExp, a).ldexp(n);
	}

	/** exponential function, exp(this)-1 */
	ddouble expm1() const pure @safe nothrow
	{
		// large this -> no need for specialized function
		if(this.abs > 0.1)
			return this.exp - 1;

		// small this -> Taylor
		return taylor!1(coeffsExp, this);
	}

	/** natural logarithm, log(this) */
	ddouble log() const pure @safe nothrow
	{
		double rhi = hi.log;
		double rlo = (this/ddouble(rhi).exp - 1).hi;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** natural logarithm, log(1+this) */
	ddouble log1p() const pure @safe nothrow
	{
		double rhi = hi.log1p;
		double rlo = (this-ddouble(rhi).expm1).hi/rhi.exp;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}


	//////////////////////////////////////////////////////////////////////
	/// trigonometric functions
	//////////////////////////////////////////////////////////////////////

	/** sine */
	ddouble sin() const pure @safe nothrow
	{
		// split this = n * pi + a
		int n = cast(int)(this / PI).hi.round;
		auto a = this - n * PI;

		// remaining a is small -> Taylor
		if(cast(uint)n % 2 == 1)
			return -a*taylor(coeffsSin, a*a);
		else
			return a*taylor(coeffsSin, a*a);
	}

	/** cosine */
	ddouble cos() const pure @safe nothrow
	{
		// split this = n * pi + a
		int n = cast(int)(this / PI).hi.round;
		auto a = this - n * PI;

		// remaining a is small -> Taylor
		if(cast(uint)n % 2 == 1)
			return -taylor(coeffsCos, a*a);
		else
			return taylor(coeffsCos, a*a);
	}

	/** tangent */
	ddouble tan() const pure @safe nothrow
	{
		return sin()/cos();
	}

	/** cotangent */
	ddouble cot() const pure @safe nothrow
	{
		return cos()/sin();
	}

	/** secant */
	ddouble sec() const pure @safe nothrow
	{
		return cos().inverse;
	}

	/** cosecant */
	ddouble csc() const pure @safe nothrow
	{
		return sin().inverse;
	}


	//////////////////////////////////////////////////////////////////////
	/// hyperbolic functions
	//////////////////////////////////////////////////////////////////////

	/** hyperbolic sine */
	ddouble sinh() const pure @safe nothrow
	{
		return -((-this.ldexp(1)).expm1/(-this).exp).ldexp(-1);
	}

	/** hyperbolic cosine */
	ddouble cosh() const pure @safe nothrow
	{
		return (this.exp + (-this).exp).ldexp(-1);
	}

	/** hyperbolic tangent */
	ddouble tanh() const pure @safe nothrow
	{
		return sinh()/cosh();
	}

	/** hyperbolic cotangent */
	ddouble coth() const pure @safe nothrow
	{
		return cosh()/sinh();
	}

	/** hyperbolic secant */
	ddouble sech() const pure @safe nothrow
	{
		return cosh().inverse;
	}

	/** hyperbolic cosecant */
	ddouble csch() const pure @safe nothrow
	{
		return sinh().inverse;
	}


	//////////////////////////////////////////////////////////////////////
	/// inverse trigonometric and hyperbolic functions
	//////////////////////////////////////////////////////////////////////

	/** inverse sine */
	ddouble asin() const pure @safe nothrow
	{
		double rhi = hi.asin();
		double rlo = (this - ddouble(rhi).sin).hi / rhi.cos;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** inverse cosine */
	ddouble acos() const pure @safe nothrow
	{
		double rhi = hi.acos();
		double rlo = (ddouble(rhi).cos - this).hi / rhi.sin;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** inverse tangent */
	ddouble atan() const pure @safe nothrow
	{
		double rhi = hi.atan();
		double rlo = (this - ddouble(rhi).tan).hi * rhi.cos^^2;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** inverse hyperbolic sine */
	ddouble asinh() const pure @safe nothrow
	{
		double rhi = hi.asinh();
		double rlo = (this - ddouble(rhi).sinh).hi / rhi.cosh;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** inverse hyperbolic cosine */
	ddouble acosh() const pure @safe nothrow
	{
		double rhi = hi.acosh();
		double rlo = (this - ddouble(rhi).cosh).hi / rhi.sinh;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}

	/** inverse hyperbolic tangent */
	ddouble atanh() const pure @safe nothrow
	{
		double rhi = hi.atanh();
		double rlo = (this - ddouble(rhi).tanh).hi * rhi.cosh^^2;
		twoSumQuick(rhi, rlo, rhi, rlo);
		return ddouble(rhi, rlo);
	}


	//////////////////////////////////////////////////////////////////////
	/// comparison
	//////////////////////////////////////////////////////////////////////

	bool isIdentical(ddouble b) const pure @safe nothrow
	{
		return hi.isIdentical(b.hi) && lo.isIdentical(b.lo);
	}

	bool opEquals(double b) const pure @safe nothrow
	{
		return hi == b && lo == 0;
	}

	int opCmp(double b) const pure @safe nothrow
	{
		if(hi > b) return 1;
		if(hi < b) return -1;
		if(lo > 0) return 1;
		if(lo < 0) return -1;
		return 0;
	}

	int opCmp(ddouble b) const pure @safe nothrow
	{
		if(hi > b.hi) return 1;
		if(hi < b.hi) return -1;
		if(lo > b.lo) return 1;
		if(lo < b.lo) return -1;
		return 0;
	}

	bool opEquals(ddouble b) const pure @safe nothrow
	{
		return hi == b.hi && lo == b.lo;
	}
}

/** std.math.round is not 'pure', so we do our own */
private double round(double x) pure @safe nothrow
{
	version(DigitalMars)
	{
		// workaround because core.stdc.math.round is not pure in DMD
		return cast(int)(x+0.5);
	}
	else
	{
		import core.stdc.math;
		return core.stdc.math.round(x);
	}
}

unittest
{
	assert(format("%.31e", ddouble(2).sqrt) == "1.414213562373095048801688724209");
	assert(format("%.29e", (ddouble(6)/ddouble(7))^^100) == "2.0198589217018753306533514440e-7");
	assert(format("%.31e", ddouble.PI.inverse) == "3.183098861837906715377675267450e-1");
}


//////////////////////////////////////////////////////////////////////
/// Basic operations with exact results. No rounding whatsoever.
//////////////////////////////////////////////////////////////////////

/**
 * NOTE: CTFE is explicitly disabled because during compile-time all doubles
 * are promoted to reals, which breaks pretty much all algorithms in this module.
 */

/** compute (hi+lo) = a + b */
private void twoSum(double a, double b, ref double hi, ref double lo) pure @safe nothrow
{
	if(__ctfe)
		assert(false, "compile-time double-double computations are not supported");

	hi = a+b;
	double v = hi-a;
	lo = (a-(hi-v))+(b-v);
}

/** compute (hi+lo) = a + b assuming abs(a) >= abs(b) */
private void twoSumQuick(double a, double b, ref double hi, ref double lo) pure @safe nothrow
{
	if(__ctfe)
		assert(false, "compile-time double-double computations are not supported");

	hi = a+b;
	lo = b-(hi-a);
}

private
{
	version(LDC)
	{
		// this will be converted to either the cpu instruction or the libm function
		pragma(LDC_intrinsic, "llvm.fma.f64")
		double fma(double, double, double) pure nothrow @trusted;
	}
	else
	{
		// always the libm function
		extern(C) double fma(double, double, double) pure nothrow @trusted;
	}
}

/** compute (hi+lo) = a * b */
private void twoProd(double a, double b, ref double hi, ref double lo) pure @safe nothrow
{
	if(__ctfe)
		assert(false, "compile-time double-double computations are not supported");

	hi = a * b;
	lo = fma(a, b, -hi);
}

/** compute (hi+lo) = a * a */
private void twoSqr(double a, ref double hi, ref double lo) pure @safe nothrow
{
	if(__ctfe)
		assert(false, "compile-time double-double computations are not supported");

	hi = a*a;
	lo = fma(a, a, -hi);
}


//////////////////////////////////////////////////////////////////////
/// Taylor series.
//////////////////////////////////////////////////////////////////////

private
{

ddouble taylor(int start = 0)(immutable(ddouble)[] c, ddouble x) pure @trusted nothrow
{
	ddouble r = x^^start * c[start];
	ddouble xi = x^^(start+1);

	for(int i = start+1; i < c.length; ++i)
	{
		ddouble s = c[i]*xi;
		ddouble t = r;
		r += s;
		if(r.isIdentical(t))
			return r;
		xi *= x;
	}

	assert(false, "some Taylor series did not converge");
}

/** exp */
immutable coeffsExp = [
	ddouble(0x1.0000000000000p+0,   0x0.0000000000000p+0),
	ddouble(0x1.0000000000000p+0,   0x0.0000000000000p+0),
	ddouble(0x1.0000000000000p-1,   0x0.0000000000000p+0),
	ddouble(0x1.5555555555555p-3,   0x1.5555555555555p-57),
	ddouble(0x1.5555555555555p-5,   0x1.5555555555555p-59),
	ddouble(0x1.1111111111111p-7,   0x1.1111111111111p-63),
	ddouble(0x1.6c16c16c16c17p-10, -0x1.f49f49f49f49fp-65),
	ddouble(0x1.a01a01a01a01ap-13,  0x1.a01a01a01a01ap-73),
	ddouble(0x1.a01a01a01a01ap-16,  0x1.a01a01a01a01ap-76),
	ddouble(0x1.71de3a556c734p-19, -0x1.c154f8ddc6c00p-73),
	ddouble(0x1.27e4fb7789f5cp-22,  0x1.cbbc05b4fa99ap-76),
	ddouble(0x1.ae64567f544e4p-26, -0x1.c062e06d1f209p-80),
	ddouble(0x1.1eed8eff8d898p-29, -0x1.2aec959e14c06p-83),
	ddouble(0x1.6124613a86d09p-33,  0x1.f28e0cc748ebep-87),
	ddouble(0x1.93974a8c07c9dp-37,  0x1.05d6f8a2efd1fp-92),
	ddouble(0x1.ae7f3e733b81fp-41,  0x1.1d8656b0ee8cbp-097),
	ddouble(0x1.ae7f3e733b81fp-45,  0x1.1d8656b0ee8cbp-101),
	ddouble(0x1.952c77030ad4ap-49,  0x1.ac981465ddc6cp-103),
	ddouble(0x1.6827863b97d97p-53,  0x1.eec01221a8b0bp-107),
	ddouble(0x1.2f49b46814157p-57,  0x1.2650f61dbdcb4p-112),
	ddouble(0x1.e542ba4020225p-62,  0x1.ea72b4afe3c2fp-120),
	ddouble(0x1.71b8ef6dcf572p-66, -0x1.d043ae40c4647p-120),
	ddouble(0x1.0ce396db7f853p-70, -0x1.aebcdbd20331cp-124),
	ddouble(0x1.761b41316381ap-75, -0x1.3423c7d91404fp-130),
	ddouble(0x1.f2cf01972f578p-80, -0x1.9ada5fcc1ab14p-135),
	ddouble(0x1.3f3ccdd165fa9p-84, -0x1.58ddadf344487p-139),
	ddouble(0x1.88e85fc6a4e5ap-89, -0x1.71c37ebd16540p-143),
	ddouble(0x1.d1ab1c2dccea3p-94,  0x1.054d0c78aea14p-149),
	ddouble(0x1.0a18a2635085dp-98,  0x1.b9e2e28e1aa54p-153),
	ddouble(0x1.259f98b4358adp-103, 0x1.eaf8c39dd9bc5p-157),
];

/** sin (odd only) */
immutable coeffsSin = [
	ddouble( 0x1.0000000000000p+0,    0x0.0000000000000p+0),
	ddouble(-0x1.5555555555555p-3,   -0x1.5555555555555p-57),
	ddouble( 0x1.1111111111111p-7,    0x1.1111111111111p-63),
	ddouble(-0x1.a01a01a01a01ap-13,  -0x1.a01a01a01a01ap-73),
	ddouble( 0x1.71de3a556c734p-19,  -0x1.c154f8ddc6c00p-73),
	ddouble(-0x1.ae64567f544e4p-26,   0x1.c062e06d1f209p-80),
	ddouble( 0x1.6124613a86d09p-33,   0x1.f28e0cc748ebep-87),
	ddouble(-0x1.ae7f3e733b81fp-41,  -0x1.1d8656b0ee8cbp-97),
	ddouble( 0x1.952c77030ad4ap-49,   0x1.ac981465ddc6cp-103),
	ddouble(-0x1.2f49b46814157p-57,  -0x1.2650f61dbdcb4p-112),
	ddouble( 0x1.71b8ef6dcf572p-66,  -0x1.d043ae40c4647p-120),
	ddouble(-0x1.761b41316381ap-75,   0x1.3423c7d91404fp-130),
	ddouble( 0x1.3f3ccdd165fa9p-84,  -0x1.58ddadf344487p-139),
	ddouble(-0x1.d1ab1c2dccea3p-94,  -0x1.054d0c78aea14p-149),
	ddouble( 0x1.259f98b4358adp-103,  0x1.eaf8c39dd9bc5p-157),
	ddouble(-0x1.434d2e783f5bcp-113, -0x1.0b87b91be9affp-167),
	ddouble( 0x1.3981254dd0d52p-123, -0x1.2b1f4c8015a2fp-177),
	ddouble(-0x1.0dc59c716d91fp-133, -0x1.419e3fad3f031p-188),
	ddouble( 0x1.9ec8d1c94e85bp-144, -0x1.670e9d4784ec6p-201),
	ddouble(-0x1.1e99449a4bacep-154,  0x1.fefbb89514b3cp-210),
	ddouble( 0x1.65e61c39d0241p-165, -0x1.c0ed181727269p-220),
	ddouble(-0x1.95db45257e512p-176, -0x1.6e5d72b6f79b9p-231),
	ddouble( 0x1.a3cb872220648p-187, -0x1.c7f4e85b8e6cdp-241),
	ddouble(-0x1.8da8e0a127ebap-198,  0x1.21d2eac9d275cp-252),
	ddouble( 0x1.5a42f0dfeb086p-209, -0x1.35ae015f78f6ep-264),
	ddouble(-0x1.161872bf7b823p-220, -0x1.bb96c8e2e8897p-275),
	ddouble( 0x1.9d4f1058674dfp-232,  0x1.03c81b6914d59p-286),
	ddouble(-0x1.1d008faac5c50p-243, -0x1.50348ded2636fp-298),
	ddouble( 0x1.6db793c887b97p-255, -0x1.966963ad60539p-314),
	ddouble(-0x1.b5bfc17fa97d3p-267,  0x1.ff5794693c028p-321),
];

/** cos (even only) */
immutable coeffsCos = [
	ddouble( 0x1.0000000000000p+0,    0x0.0000000000000p+0),
	ddouble(-0x1.0000000000000p-1,    0x0.0000000000000p+0),
	ddouble( 0x1.5555555555555p-5,    0x1.5555555555555p-59),
	ddouble(-0x1.6c16c16c16c17p-10,   0x1.f49f49f49f49fp-65),
	ddouble( 0x1.a01a01a01a01ap-16,   0x1.a01a01a01a01ap-76),
	ddouble(-0x1.27e4fb7789f5cp-22,  -0x1.cbbc05b4fa99ap-76),
	ddouble( 0x1.1eed8eff8d898p-29,  -0x1.2aec959e14c06p-83),
	ddouble(-0x1.93974a8c07c9dp-37,  -0x1.05d6f8a2efd1fp-92),
	ddouble( 0x1.ae7f3e733b81fp-45,   0x1.1d8656b0ee8cbp-101),
	ddouble(-0x1.6827863b97d97p-53,  -0x1.eec01221a8b0bp-107),
	ddouble( 0x1.e542ba4020225p-62,   0x1.ea72b4afe3c2fp-120),
	ddouble(-0x1.0ce396db7f853p-70,   0x1.aebcdbd20331cp-124),
	ddouble( 0x1.f2cf01972f578p-80,  -0x1.9ada5fcc1ab14p-135),
	ddouble(-0x1.88e85fc6a4e5ap-89,   0x1.71c37ebd16540p-143),
	ddouble( 0x1.0a18a2635085dp-98,   0x1.b9e2e28e1aa54p-153),
	ddouble(-0x1.3932c5047d60ep-108, -0x1.832b7b530a627p-162),
	ddouble( 0x1.434d2e783f5bcp-118,  0x1.0b87b91be9affp-172),
	ddouble(-0x1.2710231c0fd7ap-128, -0x1.3f8a2b4af9d6bp-184),
	ddouble( 0x1.df983290c2ca9p-139,  0x1.5835c6895393bp-194),
	ddouble(-0x1.5d4acb9c0c3abp-149,  0x1.6ec2c8f5b13b2p-205),
	ddouble( 0x1.ca8ed42a12ae3p-160,  0x1.a07244abad2abp-224),
	ddouble(-0x1.10af527530de8p-170, -0x1.b626c912ee5c8p-225),
	ddouble( 0x1.272b1b03fec6ap-181,  0x1.3f67cc9f9fdb8p-235),
	ddouble(-0x1.240804f659510p-192, -0x1.8b291b93c9718p-246),
	ddouble( 0x1.091b406b6ff26p-203,  0x1.e973637973b18p-257),
	ddouble(-0x1.bb36f6e12cd78p-215, -0x1.02f85029a29b0p-270),
	ddouble( 0x1.56457989358c9p-226, -0x1.e3792533eafc8p-282),
	ddouble(-0x1.e9d8f6ed83eaap-238,  0x1.be25ac1066519p-293),
	ddouble( 0x1.45b77f9e98e12p-249,  0x1.e4b05119ccb1bp-303),
	ddouble(-0x1.938cc661b03f6p-261, -0x1.c4da1977e56d6p-318),
];

}
