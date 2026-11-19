# Faithfully flat pullback of actual affine identity-jet functions

Let `G` be a relatively affine group scheme over `S` and let
`b : T → S`. The actual identity jets form a pullback square over
`b`. For an open `U` of `S`, `baseChangeMap_preimage_eq` identifies
the preimage of the jet open above `U` with the jet open above
`b⁻¹U`. The actual pullback of functions gives the algebra
`baseChangeSectionsAlgebra` on sections of that preimage.

Suppose `b` is affine, flat and surjective and `U` is affine.
The jet projection is affine because it is the composite of
the jet's closed immersion and the relatively affine group
projection. The actual jet base-change morphism is affine,
flat and surjective by the pullback square. Thus the jet open
and its preimage are both affine, and the existing faithful
flatness theorem for actual functions applies to their section
map. The canonical map of a faithfully flat algebra is injective,
so the actual section pullback detects equality over `U`.

This is an internal consequence of the actual jet base-change
square and affine function descent. It applies to all jet orders
and supplies the reflection of zero for the actual jet summand
in the parabolic orbit kernel comparison.
