# Polynomial normalization of real rank-one Gaussian row tests

`RealEqualPolynomialAtRank` and `RealAdjacentPolynomialAtRank` are the
rankwise polynomial-normalization properties for real character lists of the
specified lengths. The equal-rank property restricts the Schwartz row to a
polynomial Gaussian of scale \(\pi\). Both properties use the exact
Whittaker models at opposite additive scales and the supplied compatible
quotient measure.

`RealRankOnePolynomialStatement` gives the equal-rank property for two
rank-one models at every nonzero real scale. Each coefficient is a scalar
multiple of its character evaluated at the determinant. Restriction to the
line turns the row polynomial into a one-variable polynomial by evaluating
each coordinate variable at the same indeterminate. The rank-one integral
formula now gives a scalar times the real polynomial Gaussian Tate
integral, shifted by the exponent of the product character. The Tate
polynomial and the exact product character factor yield an entire
polynomial normalization on that spectral line.

This is the initial equal-rank case of the polynomial recursion in
[Jacquet, *Archimedean Rankin–Selberg integrals*, Proposition 8.1, pp. 60–61](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
