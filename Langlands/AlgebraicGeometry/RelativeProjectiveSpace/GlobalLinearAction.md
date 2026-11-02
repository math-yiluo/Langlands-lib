# Projective coordinate changes with global-function coefficients

Let `S` be any scheme and let `n` be a natural number. An invertible
linear map of the coordinate module `(Fin (n + 1) → Γ(S, ⊤))` defines
`globalLinearAction n e`, an actual automorphism of relative projective
`n`-space over `S`. It preserves the structure morphism to `S`. The
identity, composition and inverse laws follow the covariant convention:
first applying `e` and then `f` acts by `e.trans f`.

For every morphism `f : T ⟶ S`, `coordinatePullback n f` pulls back the
matrix coefficients by the ring map on global sections. It preserves
multiplication and the identity as a monoid homomorphism, and is
contravariantly functorial in `f`. Its basis coefficients are precisely
`f.appTop (e(e_j)_i)`.

The actual relative projective morphism induced by `f` commutes with
the action after pulling back its coefficients. All assertions are
equalities of scheme morphisms, including their structure-sheaf maps.
An invertible scalar global function acts as the identity. No
affineness, flatness or injectivity assumption is imposed.

This is derived internal infrastructure. The action is the existing
relative coefficient action applied to the canonical map
`S.toSpecΓ : S ⟶ Spec Γ(S, ⊤)`. The coefficient pullback is the
constructed monoid homomorphism `ProjectiveSpace.coordinateBaseChange`
for `f.appTop.hom`. Its laws use functoriality of the global-section
maps. Naturality of `S.toSpecΓ` supplies the compatibility condition
for the existing simultaneous scheme and coefficient base-change
theorem. No external source assertion is used. A nontrivial projective
bundle and the moduli scheme are separate constructions.
