# Standard polynomial Gaussians on real triangular slices

`RealSquarePolynomialMarginalStatement` starts from a square-matrix Schwartz
test that is a polynomial in the real entries times
\(\exp(-\pi\sum_{ij}A_{ij}^2)\). Right translation by any orthogonal matrix and
integration over strictly upper entries with the standard real self-dual
measure give a polynomial times the product of the standard Gaussians in the
diagonal coordinates. The diagonal polynomial's total degree is at most the
original matrix polynomial's total degree.

An orthogonal translate preserves the squared entry norm and substitutes
linear forms into the polynomial. On an upper triangular slice the squared
norm splits into the diagonal and strictly upper contributions. At fixed
upper entries the polynomial is an affine substitution in the diagonal
variables, multiplied by a scalar Gaussian value from the upper entries. For
fixed diagonal, the upper-entry parametrization is an injective affine map
with a linear part of closed range, so pulling back a Schwartz test along it
gives an integrable slice. Pointwise integration of these slices stays in the
finite-dimensional space of diagonal polynomial Gaussians of bounded degree.

This is the triangular marginal step for the square coefficient calculation
used in [Jacquet, *Archimedean Rankin–Selberg integrals*, §4.7 and §8.4](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
