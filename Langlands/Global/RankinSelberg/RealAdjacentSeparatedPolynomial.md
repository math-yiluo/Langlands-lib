# Polynomial normalization of separated real adjacent tests

`RealAdjacentUnfoldedPolynomialStatement` assumes polynomial normalizations
for the smaller equal-rank ordinary character-list tests with standard
polynomial Gaussian rows. The two smaller coefficient models have opposite
additive scales. The input to the unfolded adjacent integral is a standard
square polynomial Gaussian and a standard polynomial Gaussian row. On an
initial right half-plane the integral is a polynomial times the pair factor
of the larger character list, formed by adjoining the determinant character,
and the second smaller list.

A reproducing orthogonal weight for the square test exists because its left
translates have finite-dimensional span. Compact projection and the compact
pairing expansion express the unfolded integral as a finite sum. Each term
is the product of a smaller equal integral with the prescribed row and a
compactly paired square integral with the determinant-character twist. The
smaller hypothesis and the square polynomial theorem give a polynomial for
each factor. The reciprocal pair factor after adjoining the character is
the product of the two reciprocals used in each term.

`realAdjacentSeparatedPolynomial` applies the initial corank-one unfolding
to the actual Godement coefficient of a square-column product. It assumes
that the Fourier transform of the column test is a standard polynomial
Gaussian row. The Weyl scalar is absorbed into the normalization polynomial.

This is the separated-test step of the polynomial recursion in
[Jacquet, *Archimedean Rankin–Selberg integrals*, §8.3–§8.4, pp. 58–61](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
