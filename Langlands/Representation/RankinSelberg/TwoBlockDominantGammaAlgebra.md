# Rational algebra for the equal-rank gamma product

This internal development identifies the existing Laurent clearing unit with
the quotient of the first epsilon monomial by the reflection of the second.
It separates the block minus-one signs using the second sign's square-one law.
It then divides the retained rational comparison by the nonzero polynomial
factors and uses a supplied reciprocal dual-gamma relation to obtain the
product gamma equation. All analytic comparisons and nonvanishing premises are
explicit; this module supplies only the rational algebra.

`ReflectedGammaProductLaw` packages the final implication over all four block
polynomials and all three rational functions. Its proof assumes only that the
second block sign has square one. The original first polynomial may be zero;
the dual first polynomial and both second polynomials must be nonzero. The
proof uses their nonzero rational images, the reciprocal second gamma relation,
and field algebra to cancel exactly the displayed factors. The complete
induced gamma-factor identification is a further analytic assembly step.

The provenance is internal: the Laurent multiplier and reflection definitions
are imported from the numerator modules, and the epsilon and gamma expressions
come from `PairFactors`. No new literature assertion is translated here.
