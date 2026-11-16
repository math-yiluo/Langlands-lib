# Determinant-sign correction for signed real reversal

This internal helper defines the complex-valued determinant sign
`signDet g = det(g)/|det(g)|` and the complex-linear map
`signedTwistLin q f g = signDet(g)^q f(twist(g))` on functions on `GL₃(ℝ)`.
It uses the signed reversal of `RealMixedSwapTwist` and the sign character
`unitSign` of `RealMixedSwapParameters`.

The determinant sign is multiplicative, squares to one, and is unchanged
by inversion and by the twist. The signed pullback is consequently an
involution. Smoothness follows by expressing determinant sign as the quotient
of the determinant by its absolute value on invertible matrices, where the
denominator is nonzero, and then using smooth products and composition.

Right orthogonal translation commutes with signed pullback up to the scalar
`signDet(k)^q`. Each translated function therefore lies in the linear image
of the original finite orbit span, proving preservation of orthogonal
finiteness. Every plane rotation has determinant sign one: a rotation
is the square of the rotation through half its angle, and determinant
sign squares to one. Thus the sign factor can be taken outside the
Fourier integral. The two rotation planes are exchanged with the same
integer Fourier index.

On diagonal matrices determinant sign is the product of the coordinate
signs; on upper unipotent matrices it is one. Combining these facts with
the unsigned principal-series transport proves that the new character list is
`χ'_j(x) = unitSign(x)^q χ_(2-j)(x⁻¹)`, for `j : Fin 3`.
The same transport preserves the orthogonal finite part of the principal
series.

Provenance is internal algebraic and differential transport from the
published Library definitions. No irreducibility, mixed-swap existence,
or Lie-intertwining result is assumed by this construction.
