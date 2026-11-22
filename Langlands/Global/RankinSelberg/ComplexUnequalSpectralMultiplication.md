# Spectral multiplication for ordinary complex unequal-rank integrals

The positive diagonal with first entry `exp(x)` respects padding and
multiplies the normalized absolute determinant by `exp(2*x)`. Right
translation on the smaller unipotent quotient preserves its compatible
measure. Translating both Whittaker vectors by their respective diagonals
therefore multiplies the ordinary integral by the inverse determinant
power. Differentiation of the translated coefficient is the right Lie
derivative in the first diagonal matrix direction.

For the derivative under the integral, use a compact interval of dilation
parameters. The root bounds for the two Lie derivatives are uniform on the
corresponding compact families of translates. Ordinary half-plane domination
then permits differentiation in the real dilation parameter. The derivative
of the determinant multiplier is `-2 * (s - (r-t)/2)`. Thus the sum of the two
ordinary integrals with one coefficient differentiated is that affine
function of `s` times the original integral.

This is a derived spectral multiplication identity for the ordinary integral
(2.4) of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), author p. 6.
It gives the multiplication-by-variable operation used for the polynomial
ideal in §15, author pp. 108–109, once the test values are polynomials.

`complexUnequalFiniteSumFromPolynomials` uses the derivative identity to
prove stability of the complex span of the test polynomials under
multiplication by the spectral variable. A common right half-plane
allows cancellation of the reciprocal L-factor. The resulting equality
of polynomial evaluations on infinitely many points gives the identity
in the polynomial ring. The principal-ideal argument produces an actual
finite sum equal to one from polynomial normalizations and pointwise
coverage.
