# Integral prescribed opposite factors from translated cell coordinates

This internal composition identifies prescribed normalizing opposite factors
with integral dynamic cell coordinates in the original ambient model. It
retains arbitrary universe `u`.

Let `A` be a domain, `K` a supplied fraction field, and `M` an integral model
of an affine group scheme `G` over `K`. Supply a scheme-monic morphism
`i : T.toGrp → G` from a split torus, an actual relative root `a`, and
`HasRelativeRootSystem i`. Choose a torus cocharacter `ν` with positive pairing
with `a`, and an actual cocharacter `χ` of `M.group` whose base change followed
by `M.genericIso.hom` equals `ν` composed with `i`. Supply actual integral
representatives `j` and `r` of the dynamic unipotent subgroup of the opposite
of `χ` and the dynamic parabolic of `χ`.

Let `m` be an integral section whose exact generic image is an actual rational
normalizer `n` representing the reflection of `a`. Let `x` be an integral
section with nonidentity generic image in `U_a`, and `p = (p₁,p₂)` a prescribed
`IsOppositeFactorPair i a (M.integralPointMap x)`: both factors lie in `U_{-a}`
and `p₁ (M.integralPointMap x) p₂` normalizes the torus.

`integral_first_oppositeFactor_of_cell_lift` assumes actual integral coordinates
in the `j,r` cell for `x m⁻¹`. The prescribed-pair translated-cell construction
gives generic factors with first factor `p₁⁻¹`, belonging to the dynamic
opposite unipotent and parabolic of the generic cocharacter. Its product is
the generic image of `x m⁻¹`. The ambient dynamic factor theorem identifies
both with integral images; inversion yields integrality of `p₁`.

`integral_oppositeFactors_of_cell_lifts` assumes integral cell coordinates
for both `x m⁻¹` and `x⁻¹ m⁻¹`, using the same `m`. It applies the first-factor
result to `x` and then to `x⁻¹` with the reversed inverse pair
`(p₂⁻¹,p₁⁻¹)`. That pair is an opposite factor pair because its normalizer
product is the inverse of the original one. This proves that both original
prescribed factors belong to `M.integralPoints`.

`integralPrescribedOppositeFactorLift` selects integral sections mapping exactly
to the two original factors, with both equalities recorded in its subtype.

The provenance is internal composition of
`IsOppositeFactorPair.translatedCellFactorPair`, the exact cocharacter
comparison, `integral_dynamic_factors_of_cell_lift`, and closure of actual
root, normalizer and integral-point subgroups under inversion. The construction
assumes the two integral cell coordinates and the integral reflection
representative. It does not construct rank-one reduction data, an integral
model at a building point, or prove the host fixed-point opposite-factor
statement.
