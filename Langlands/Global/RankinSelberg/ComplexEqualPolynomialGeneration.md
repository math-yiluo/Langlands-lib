# Polynomial Gaussian row tests under radial differentiation

A standard row test is a polynomial in the real and imaginary parts of
the entries times a fixed Gaussian. A polynomial in the entries and
their complex conjugates has this form by a linear change of variables.

The radial derivative of the polynomial factor is polynomial, by the
product rule on each coordinate. The derivative of the Gaussian
multiplies it by minus twice its scale times the squared row norm.
This norm is itself a polynomial in the real and imaginary coordinates.
Thus the radial derivative keeps the scale and again gives a standard
row Schwartz test.

`complexEqualFiniteSumFromPolynomials` assumes polynomial normalizations
for the equal-rank tests of this form and pointwise coverage by these tests.
The quotient identity with the radial derivative realizes multiplication
by an affine polynomial with nonzero leading coefficient. The principal
ideal argument gives a finite sum equal to one. The chosen tests keep their
polynomial Gaussian rows when regarded as ordinary equal-rank tests.

This is a derived step for Jacquet, *Archimedean Rankin–Selberg integrals*
(2009), Proposition 8.1(ii), author pp. 60–61, and Theorem 2.7(ii), author
p. 10 with proof in §15, pp. 108–109. The Library's row coordinates are
real and imaginary parts, which are complex linear combinations of the
entries and their conjugates.
