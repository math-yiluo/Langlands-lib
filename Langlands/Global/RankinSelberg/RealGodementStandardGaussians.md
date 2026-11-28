# Standard polynomial Gaussians on real rectangles

`RealGodementStandardGaussianSplitStatement` identifies the rectangular test
obtained by precomposing a scale-one polynomial Gaussian by multiplication
by `√π`. It is the sum over the monomial support of the multiplier. Each
summand is a product of a polynomial Gaussian on the leading square block
and a monomial Gaussian on the last column, both dilated by the same scalar.

The proof uses the separation of the monomials in `RealAdjacentGaussianSplit`.
Precomposition multiplies every polynomial variable by `√π` and scales the
sum of squares by `π`. `standardMatrixTest_eq_squarePolynomialGaussian` and
`standardColumnTest_isGaussianPolynomialRow` express the square and column
factors in the respective scale-π classes. The separation implements the
standard test decomposition in Jacquet, *Archimedean Rankin–Selberg
Integrals*, §8.4, Proposition 8.1, pp. 60–61.
