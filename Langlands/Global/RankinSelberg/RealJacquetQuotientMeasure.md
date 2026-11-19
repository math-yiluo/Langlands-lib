# Quotient-measure independence of the real equation packages

`RealJacquetQuotientMeasureIndependenceStatement` says that the unequal- and
equal-rank equation packages each hold for one compatible quotient measure
exactly when they hold for any other compatible quotient measure on the same
quotient. The functions, additive parameters, L-factors, epsilon, and sign
are fixed. This permits the use of one chosen compatible quotient measure
in a proof of the real local equations.

Compatibility supplies regularity, nonzero mass, and right invariance for the
two quotient measures. The published comparison of right-invariant measures on
the quotient by a closed subgroup gives a positive finite scalar relating them.
The real upper unipotent subgroup is closed and its compatible Haar measure is
right invariant.

In the unequal-rank package, the rectangular self-dual measure is fixed, so
the product measure for absolute convergence picks up only the quotient
scalar. The outer integral in the iterated dual integral picks up that same
scalar. In equal ranks both integrals use the quotient measure directly.
`EquationPackage.smul_measures` then keeps the abscissa, rescales the two
continuation witnesses, and multiplies both sides of the codiscrete equation
by the same scalar. Applying the transport in both directions gives the two
equivalences.

This is an internal normalization lemma for the Library's versions of the
integrals in Jacquet (2.4)–(2.6) and Theorem 2.1. The hypotheses and proof
use the Library's compatible quotient measures and the existing real
equation packages. [Jacquet, *Archimedean Rankin–Selberg Integrals*, p. 6](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
