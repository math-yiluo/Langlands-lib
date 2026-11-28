# Polynomial normalization of compactly paired real square tests

`RealCompactSquarePolynomialStatement` concerns a vector in the real position
principal series of a character list. Pair its left translates against a
continuous complex weight on a compact topological group with a continuous
homomorphism into the orthogonal group. The compact measure is a supplied
finite Borel measure. With a standard polynomial Gaussian matrix test, a
real determinant-character twist, and the supplied general linear group Haar
measure, the square integral converges absolutely in a right half-plane.
There it equals a polynomial times the pair factor of the determinant
character and the inducing list.

The left translates of the polynomial Gaussian stay in the space given by
the same total degree bound. The weighted compact average therefore has a
polynomial multiplier at the same Gaussian scale. The principal-series
height estimate bounds the compactly translated coefficients uniformly,
since left orthogonal multiplication preserves the matrix height. Fubini
and Haar left invariance move the compact pairing from the coefficient to
the test. The resulting integral is the square zeta integral of a
principal-series vector and the averaged polynomial Gaussian, to which
`realSquareZetaPolynomial` applies. Twisting the vector replaces each
inducing character by its product with the determinant character. The
compact weight is adjusted by the inverse character on the compact group,
and the resulting torus product is the specified pair factor.

The calculation supplies the square factor in the polynomial recursion of
[Jacquet, *Archimedean Rankin–Selberg integrals*, §8.4, pp. 60–61](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).

`RealCompactSquarePolynomialConclusion` denotes the integral assertion before imposing the compact topological group and Borel hypotheses.
