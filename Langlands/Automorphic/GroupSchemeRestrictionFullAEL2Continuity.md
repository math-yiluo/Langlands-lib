# Joint continuity and Bochner integration on the a.e. cuspidal L² subspace of `[G]`

Author: Worker 112.

The published module `GroupSchemeRestrictionFullAEL2` defines the
almost-everywhere cuspidal subspace `quotientFullAEL2CuspidalSubmodule` of `L²`
of the restriction split-centre quotient `RestrictionSplitCentre.Quotient F G S j`.
This quotient has the shape `[G] = A_G G(F) \ G(A_F)` of Getz--Hahn
(2.20)--(2.21) (`getz-hahn-2024-automorphic-representations`, printed
pp. 68--69). The subspace follows their (6.20)--(6.21) (printed p. 168). The
published `GroupSchemeRestrictionFullAEL2Hilbert` makes it a Hilbert space with
an orthogonal projection. The published `GroupSchemeRestrictionQuotientL2Continuity`
proves joint continuity of the right action on all of `L²([G])` and constructs
the Bochner integrated action there.

The present module restricts both constructions to the cuspidal subspace. It is
the `[G]` counterpart of the published positive-torus modules
`GroupSchemeFullAEL2Continuity` and `GroupSchemeFullAEL2Integrated`, and it
proves that the published `fullAEL2CuspidalEquiv` carries the positive-torus
integrated action to the `[G]` one.

## Data and hypotheses

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type. `hG : IsConnectedReductive G`, and
  `hPD : ParabolicDynamicStatement.{0}` is the structural hypothesis taken by
  the published cuspidal subspace.
- `S` is a commutative group scheme over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`.
- `T` is a commutative group scheme over `F` and `i : T.toGrp ⟶ G`, with
  `h : subgroup F G S j = imageSubgroup F T G i`.
- `characterRestrict i` is injective (`hi`) with finite-index range,
  `hc : IsCentral i`, and `hT : IsSplitTorus T.toGrp`.
- Haar measure on `normOneSubgroup F G` is right invariant (an instance
  argument), and `hInv'` is any proof of
  `QuotientRightInvariant F G μ`, where `μ = quotientHaarMeasure F G S j`.

Write `Sq` for `quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT`,
`R(g)` for the published `rationalQuotientL2RightAction` on `Lp ℂ 2 μ`, and
`Rc(g)` for its published restriction `quotientFullAEL2CuspidalRightAction`
to `Sq`.

## Joint continuity and bounded operators

- `quotientFullAEL2CuspidalJointRightAction` is the element of
  `C(AdelicGroupPoints F G × Sq, Sq)` given by `(g, φ) ↦ Rc(g) φ`. Its
  continuity is the published `rationalQuotientL2JointRightAction`, composed
  with the identity times the subtype inclusion, and then corestricted to the
  subtype. The `_apply` lemma holds by definition.
  `quotientFullAEL2CuspidalJointRightAction_val` states that forgetting the
  subtype gives the published joint action on `L²([G])`, also by definition.
- `quotientFullAEL2CuspidalOrbitMap φ` is the continuous orbit map
  `g ↦ Rc(g) φ`.
- `quotientFullAEL2CuspidalBoundedRightAction` is the group homomorphism from
  the adelic points to `Sq →L[ℂ] Sq`, sending `g` to the bounded map of the
  published isometry `quotientFullAEL2CuspidalRightTranslate`. The identity and
  multiplication laws reduce through the subtype to the published
  `rationalQuotientL2RightTranslate_one` and `rationalQuotientL2RightTranslate_mul`.
  `norm_quotientFullAEL2CuspidalBoundedRightAction` proves `‖Rc(g) φ‖ = ‖φ‖`.

## Bochner integration

Let `ν` be any measure on `AdelicGroupPoints F G` and let
`f : AdelicGroupPoints F G → ℂ` satisfy `hf : Integrable f ν`. Write `A` for
the published `rationalQuotientL2IntegratedAction`, the operator
`φ ↦ ∫ g, f g • R(g) φ ∂ν` on `L²([G])`.

- `quotientFullAEL2CuspidalOrbit_aestronglyMeasurable` proves that each
  cuspidal orbit is almost everywhere strongly measurable for `ν`, because the
  orbit map is continuous. Separability of `Sq` is not assumed.
- `quotientFullAEL2CuspidalActionIntegrand_integrable` proves Bochner
  integrability in `Sq` of `g ↦ f g • Rc(g) φ`, by the published
  `isometricActionIntegrand_integrable`. The integral is formed in `Sq`, which
  is complete by the published `GroupSchemeRestrictionFullAEL2Hilbert`.
- `coe_integral_quotientFullAEL2CuspidalRightAction` proves that the
  `Sq`-valued integral, viewed in `L²([G])`, equals `A φ`. The proof moves the
  isometric inclusion inside the integral with Mathlib's
  `LinearIsometry.integral_comp_comm`.
- `rationalQuotientL2IntegratedAction_mem_quotientFullAEL2CuspidalSubmodule`
  concludes that `A` maps `Sq` into `Sq`.
- `quotientFullAEL2CuspidalIntegratedAction` is the corestriction of `A` to an
  element of `Sq →L[ℂ] Sq`. `quotientFullAEL2CuspidalIntegratedAction_val`
  states that forgetting the subtype gives `A`, by definition.
  `quotientFullAEL2CuspidalIntegratedAction_apply` states that its value is
  the `Sq`-valued integral `∫ g, f g • Rc(g) φ ∂ν`.
  `norm_quotientFullAEL2CuspidalIntegratedAction_le` bounds its operator norm
  by `∫ g, ‖f g‖ ∂ν`, using the published bound for `A`.
- `quotientFullAEL2CuspidalOrthogonalProjection_integratedAction` proves that
  the published orthogonal projection onto `Sq` carries `A φ` to the
  integrated cuspidal action applied to the projection of `φ`, for every
  `φ` in `L²([G])`. The proof moves the continuous linear projection inside
  the integral with Mathlib's `ContinuousLinearMap.integral_comp_comm`, then
  applies the published equivariance
  `quotientFullAEL2CuspidalOrthogonalProjection_rightAction` under the integral.
  `quotientFullAEL2CuspidalAmbientProjection_integratedAction` gives the
  corresponding identity for the ambient projection: it commutes with `A`.

These are equalities of `L²` classes. The measure `ν` is arbitrary, and no
Haar property or convolution identity for it is asserted.

## Comparison with the positive-torus quotient

`fullAEL2CuspidalEquiv_integratedAction` takes explicit splitting coordinates
`I` and `e : T.toGrp ≅ splitTorus (Spec F) I` in place of `hT`. It proves
that the published isometric equivalence
`fullAEL2CuspidalEquiv F G hPD hG h hi I e hc` carries the published
positive-torus `fullAEL2CuspidalIntegratedAction` to
`quotientFullAEL2CuspidalIntegratedAction`, where the split-torus proof is the
one built from `I` and `e`. On underlying `L²` classes this is the published
`quotientL2Equiv_integratedAction`, applied after the published
`fullAEL2CuspidalIntegratedAction_val`.

## Split components

Assume `hj : IsSplitComponent j` and `hs : IsSplitComponent i`, injectivity and
finite index of `characterRestrict i`, and the norm-one right-invariance
instance. The comparison equality is the published
`subgroup_eq_of_splitComponents`, right invariance of `μ` is the published
`quotientHaarMeasure_rightInvariant_of_splitComponents`, and centrality and the
split-torus property come from `hs`.

- `splitComponentFullAEL2CuspidalJointRightAction` is the joint action on the
  published `splitComponentFullAEL2CuspidalSubmodule`; its `_val` lemma
  recovers the published `splitComponentL2JointRightAction`.
- `splitComponentFullAEL2CuspidalIntegratedAction` is the integrated action on
  that subspace; its `_val` lemma recovers the published
  `splitComponentL2IntegratedAction`, and
  `norm_splitComponentFullAEL2CuspidalIntegratedAction_le` gives the bound
  `∫ g, ‖f g‖ ∂ν`.
- `splitComponentFullAEL2CuspidalOrthogonalProjection_integratedAction` states
  that the published split-component orthogonal projection intertwines the
  integrated actions.

This section keeps the norm-one right-invariance instance as a hypothesis. For
connected reductive `G` it can be supplied by the published
`normOneHaar_isMulRightInvariant_of_connectedReductive`; this module does not
invoke it.

## Provenance and scope

The quotient follows Getz--Hahn (2.20)--(2.21) and the cuspidal subspace their
(6.20)--(6.21). Every construction here is internal: it restricts the published
joint and integrated actions on `L²([G])` to the published cuspidal subspace,
using pinned Mathlib's continuity API for products and subtypes and its
commutation of Bochner integrals with linear isometries and continuous linear
maps. No literature theorem is attributed to this module.

This module does not prove existence of split components, injectivity or finite
index of `characterRestrict i`, `ParabolicDynamicStatement`, finite volume,
density of smooth or continuous vectors, convolution identities, compactness,
trace-class properties or any spectral decomposition.
