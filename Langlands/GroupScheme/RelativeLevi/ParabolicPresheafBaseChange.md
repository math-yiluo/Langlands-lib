# Canonical base change of the actual parabolic presheaf

This derived prerequisite compares the actual parabolic presheaves before and
after arbitrary change of base. It does not construct a representing scheme.

For an ambient group-scheme isomorphism `e : H ≅ J`, `ambientEquiv e` identifies
actual parabolic subgroup functors by inverse-image along `e.inv`; its inverse
uses `e.hom`. Relative parabolicity is preserved by the already proved ambient
transport theorem, and the inverse laws follow from functoriality of subgroup
inverse-image.

For `b : S' ⟶ S` and `T : Over S'`, `baseChangeEquiv b T` uses the canonical
isomorphism from the iterated ambient pullback to the direct pullback along
`T.hom ≫ b`. Thus it identifies actual parabolic subgroup functors of these two
group schemes. `baseChangeEquiv_val` states its exact all-test inverse-image
formula, and `baseChangeEquiv_range` identifies the image of any represented
subgroup with the range of its actual pushed family.

`restrict_baseChangeEquiv` proves compatibility with every parameter morphism.
The proof chooses an actual relative parabolic representative, expresses both
restrictions as actual family evaluations, and applies the existing
`TorusSubgroupModuli.familyHom_pushFamily` comparison. Consequently,
`parabolicPresheafBaseChangeIso b hG` is a natural isomorphism from the actual
parabolic presheaf of the pulled-back reductive group to the original presheaf
precomposed with `(Over.map b).op`. The values remain in `Type (u + 1)` and no
smallness, closedness, flatness or cover hypothesis on `b` is required.

All constructions are internal consequences of the imported Library family
comparison and relative parabolic transport results. No new literature claim is
used. Smooth proper representability remains a separate obligation.
