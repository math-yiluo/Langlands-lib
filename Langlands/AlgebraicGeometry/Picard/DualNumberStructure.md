# Structure sheaf of the actual dual-number thickening

Let `k` be a field in an arbitrary universe, `X` a scheme in the same universe,
and `f : X ⟶ Spec k`. Write `P = DualNumberThickening.thickening f`, with actual
projection `p : P ⟶ X` and second projection `q : P ⟶ Spec (DualNumber k)`.
For every open `U` of `X`, this module constructs the canonical ring equivalence

`sectionEquiv f U : DualNumber Γ(X, U) ≃+* Γ(P, p ⁻¹ᵁ U)`.

Its forward map is `sectionMap f U`. If `z = a + epsilon b`, its formula is
`p.app U a + p.app U b * epsilonSection f U`, where `epsilonSection` is the
pullback of the actual epsilon section along `q`. In particular it sends `inl a`
to `p.app U a`, and epsilon to `epsilonSection f U`.

The maps commute with restriction: `sectionMap_naturality` expresses this as
an equality of ring homomorphisms. They form `structureComparison`, a natural
transformation from the coefficientwise dual-number presheaf `splitPresheaf` to
`actualPresheaf`, the actual structure presheaf of `P` pushed forward along `p`.
Both presheaves are sheaves. The same morphism is `sheafComparison`, and
`sheafComparison_isIso`, `structureComparison_isIso`, and `sectionMap_isIso`
prove these comparisons are isomorphisms.

## Implemented construction and proof

`dualNumberFunctor` applies the published coefficient ring map to each
coordinate. The actual second projection and `Scheme.ΓSpecIso` define
`testSectionMap`. Its value at epsilon is square-zero because it is a ring
homomorphism. The universal property `DualNumber.lift`, using `p.app U` as the
coefficient algebra, then defines `sectionMap`. Naturality follows from the
restriction identities of the two actual scheme projections. The split
presheaf satisfies the sheaf condition by gluing its two coordinates separately.

The projection `p` is affine by base change of the affine morphism from the
dual-number spectrum to the field spectrum. The restriction of the pullback to
any open of `X` remains a pullback, by pasting the restriction square with the
original square. For an affine open `U`, Mathlib's
`isPushout_appTop_of_isPullback` identifies its rings of global sections as a
pushout. `affine_isPushout` transports that square along `ΓSpecIso` and the
canonical `U.topIso`, so its maps are precisely `baseSectionMap f U`, the base
field inclusion into the dual numbers, `p.app U`, and `testSectionMap f U`.

`split_isPushout` transports the standard tensor-product pushout along the
published `DualNumberBaseChange.tensorEquiv`. The unique isomorphism between
these two pushouts agrees with `sectionMap`: agreement on the coefficient ring
and on epsilon suffices by `DualNumber.ringHom_ext`. This proves
`affine_sectionMap_isIso`.

Finally, the target sheaf is the pushforward of the actual structure sheaf.
Mathlib's `TopCat.Sheaf.isIso_iff_isIso_basis`, applied to `X.isBasis_affineOpens`,
extends the affine result to the sheaf comparison and hence every open.
`sectionEquiv` is the ring equivalence obtained from the resulting categorical
isomorphism, with the same forward map.

## Provenance and scope

This is an internal construction derived from the published actual thickening,
its affine tensor comparison, and Mathlib's pullback, pushout, restriction and
sheaf-basis universal properties. No geometric comparison is assumed as a
hypothesis. The field, scheme and open are arbitrary; no quasi-compactness,
separation, finite-type, smoothness, or algebraic-closure hypothesis is imposed.

This module establishes the structure-sheaf comparison only. Compatibility with
the zero-section reduction, the actual unit-kernel comparison, classification
of deformations of line bundles, and the tangent-to-derived-H1 theorem are
separate subsequent obligations. The published target and its imports are
unchanged.
