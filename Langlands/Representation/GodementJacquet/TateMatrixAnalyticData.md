# Rank-one matrix analytic data from scalar action

`TateCharacterAction σ χ` means that the specified continuous character of the
field units acts by scalars through the determinant on the actual carrier.
This internal derived module proves actual matrix convergence, rationality and
normalized-generator existence from a continuous character acting by scalars on
the specified smooth, nonzero representation. It also proves equality of the
matrix and scalar rational-value families before Laurent span. No character
reduction or Fourier equation is assumed or asserted here.

All left translates of the character lie in its one-dimensional span, so
`TateScalarMellin` supplies one half-plane for every scalar test, rational
continuations and a common denominator. Scalar action determines every actual
bi-smooth matrix coefficient by its value at the identity. Exact canonical Haar
transport in `TateScalarTransport` identifies its matrix integral with the scalar
Mellin integral after multiplying the scalar test by that value. The rank-one
JPSS shift is zero. The half-plane is chosen before the test and coefficient.

For the reverse inclusion of value families, smooth-dual separation supplies a
coefficient nonzero at the identity. Dividing by that value gives the character
itself as an actual bi-smooth coefficient; the full-matrix scalar homeomorphism
lifts every scalar test. The common denominator therefore transfers to the
matrix family. The published attained unit value and normalized-generator
existence theorem supply its normalized polynomial.

In rank one inverse transpose is inversion, so pullback acts by the inverse
character on the same carrier. Smoothness pulls back by the continuous
automorphism. The published coefficient-space transport identifies the original
inverse-transpose value family and analytic predicate with the ordinary ones of
this pullback. The same arguments therefore give transformed convergence,
rationality, a normalized polynomial, and equality with the inverse-character
scalar Mellin family. No identification with a contragredient is needed.
