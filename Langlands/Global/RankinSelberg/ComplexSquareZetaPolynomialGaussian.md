# Polynomial normalizations of standard complex square coefficient integrals

The standard square Gaussian has scale \(2\pi\). Its polynomial
multipliers can be expressed in the real and imaginary matrix coordinates.
Right unitary multiplication preserves the squared matrix norm and acts
linearly on the coordinates. A weighted compact average therefore stays in
the finite-dimensional space of polynomial Gaussians of bounded degree.

On a fixed upper triangular slice, the matrix norm splits into its diagonal
and strictly upper parts. Fixing the strictly upper entries gives an affine
substitution in the diagonal coordinates, so their polynomial degree is
bounded by the matrix degree. The upper triangular marginal integrates a
pointwise integrable family in this finite-dimensional diagonal space.

The square zeta comparison identifies the product Tate normalization of
this marginal with the original square integral times the reciprocal
standard factor on a right half-plane, up to the fixed Haar constant.
The diagonal Tate polynomial theorem gives the required polynomial, with
degree at most the matrix polynomial degree.

This implements the square coefficient calculation in Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §4.7, equations
(4.3)–(4.4), author pp. 30–31, and Remark 4.4, author p. 30, as
used in the proof of Proposition 8.1 in §8.4, author pp. 60–61.
