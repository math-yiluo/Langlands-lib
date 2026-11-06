# Joint continuity and Bochner integration of the restriction quotient L² action

Author: Worker 112.

The published module `GroupSchemeRestrictionQuotientL2` defines the right
regular representation `rationalQuotientL2RightAction` on `L²` of the
restriction split-centre quotient `RestrictionSplitCentre.Quotient F G S j`.
This is the quotient `[G] = A_G G(F) \ G(A_F)` of Getz--Hahn (2.20)--(2.21)
(`getz-hahn-2024-automorphic-representations`, printed pp. 68--69). The same
module gives the linear isometric equivalence `quotientL2Equiv F G h` from `L²`
of the positive-torus quotient. For the positive-torus quotient, the published
modules `GroupSchemeQuotientL2Continuity` and `GroupSchemeQuotientL2Integrated`
already prove joint continuity of the right action and construct the Bochner
integrated action `φ ↦ ∫ f(g) R(g) φ dν(g)`. The present module carries both
constructions over to the restriction quotient, conjugating by
`quotientL2Equiv`.

## Data

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- `S` is a commutative group scheme over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G` maps it into the Weil
  restriction.
- `T` is a commutative group scheme over `F` and `i : T.toGrp ⟶ G`.

Write `ν⁺ = positiveRationalQuotientHaarMeasure F G T i` and
`μ = quotientHaarMeasure F G S j`. `hInv'` is an arbitrary proof of
`QuotientRightInvariant F G μ`. The published
`quotientHaarMeasure_rightInvariant` supplies one, and every result here holds
for whichever proof is given.

## Bounded operators

For any measure `measureQ` on `Quotient F G S j` with
`hInv : QuotientRightInvariant F G measureQ`:
- `rationalQuotientL2BoundedRightAction F G measureQ hInv` is the group
  homomorphism from the adelic points to bounded operators on
  `Lp ℂ 2 measureQ`. Its value at `g` is the continuous linear map of the
  isometry `rationalQuotientL2RightTranslate F G measureQ hInv g`. The group
  laws are the published `rationalQuotientL2RightTranslate_one` and
  `rationalQuotientL2RightTranslate_mul`.
- `rationalQuotientL2BoundedRightAction_apply` states that it evaluates to
  `rationalQuotientL2RightAction`. This holds by definition.
- `norm_rationalQuotientL2BoundedRightAction` proves `‖R(g) φ‖ = ‖φ‖`.

No comparison hypothesis or split-torus data is needed for this section.

## Conjugation and joint continuity

Assume `h : subgroup F G S j = imageSubgroup F T G i`. Assume also that
`characterRestrict i` is injective with finite-index range. Assume
`hc : IsCentral i` and that Haar measure on `normOneSubgroup F G` is right
invariant.

- `rationalQuotientL2RightAction_eq_quotientL2Equiv` additionally takes
  explicit splitting coordinates `I` and
  `e : T.toGrp ≅ splitTorus (Spec F) I`. It proves
  `R(g) φ = E (R⁺(g) (E.symm φ))`, where `E = quotientL2Equiv F G h` and `R⁺`
  is the published `quotientL2RightAction` for `ν⁺`. The right invariance of
  `ν⁺` used by `R⁺` is the published `haarQuotientMeasureRightInvariant` for
  these coordinates. The proof rewrites with the published
  `quotientL2Equiv_rightAction`.
- `continuous_rationalQuotientL2RightAction_of_splitData` proves that
  `(g, φ) ↦ R(g) φ` is continuous on `AdelicGroupPoints F G × Lp ℂ 2 μ`, for the
  same explicit coordinates. By the previous result, the map is `E`, composed
  with the published continuous map `haarQuotientL2JointRightAction`, composed
  with `(g, φ) ↦ (g, E.symm φ)`. All three are continuous.
- `continuous_rationalQuotientL2RightAction` replaces the coordinates by
  `hT : IsSplitTorus T.toGrp`. It extracts a finite index type and an
  isomorphism from `hT`.
- `rationalQuotientL2JointRightAction` packages the action as an element of
  `C(AdelicGroupPoints F G × Lp ℂ 2 μ, Lp ℂ 2 μ)`.
  `rationalQuotientL2OrbitMap φ` restricts it to the fixed vector `φ`, giving
  an element of `C(AdelicGroupPoints F G, Lp ℂ 2 μ)`. The `_apply` lemmas
  hold by definition.

## Bochner integration

Keep the hypotheses of the previous section, with `hT` in place of the
coordinates. Let `ν` be any measure on `AdelicGroupPoints F G`. Let
`f : AdelicGroupPoints F G → ℂ` satisfy `hf : Integrable f ν`.

- `rationalQuotientL2Orbit_aestronglyMeasurable` proves that each orbit
  `g ↦ R(g) φ` is almost everywhere strongly measurable for `ν`. The orbit is
  the continuous map `rationalQuotientL2OrbitMap φ`, and pinned Mathlib proves
  strong measurability of continuous maps here because the adelic group is
  second countable with its Borel structure. Separability of `L²` is not
  assumed.
- `rationalQuotientL2ActionIntegrand_integrable` proves Bochner integrability
  of `g ↦ f(g) • R(g) φ`. It applies the published
  `isometricActionIntegrand_integrable` from
  `Representation.Unitary.IntegratedOperator`.
- `rationalQuotientL2IntegratedAction F G hInv' h hi hc hT ν f hf` is the
  bounded complex-linear operator obtained from the published
  `integratedIsometricAction`.
  `rationalQuotientL2IntegratedAction_apply` states its value
  `∫ g, f g • R(g) φ ∂ν`, by definition.
- `norm_rationalQuotientL2IntegratedAction_le` bounds its operator norm by
  `∫ g, ‖f g‖ ∂ν`, by the published `integratedIsometricAction_norm_le`.
- `quotientL2Equiv_integratedAction` takes explicit coordinates `I`, `e`. It
  proves that `E` carries the published `haarQuotientL2IntegratedAction` for
  `ν⁺` to `rationalQuotientL2IntegratedAction`. The proof moves `E` inside the
  Bochner integral with Mathlib's `LinearIsometry.integral_comp_comm`. It then
  applies `quotientL2Equiv_rightAction` under the integral.

The measure `ν` is arbitrary. No Haar property or convolution identity for it
is asserted. In particular it may be specialized to the inverse of canonical
group Haar measure, as in the positive-torus module.

## Split components

Assume `hj : IsSplitComponent j` and `hs : IsSplitComponent i`. Assume also
that `characterRestrict i` is injective with finite-index range and that Haar
measure on `normOneSubgroup F G` is right invariant. The comparison equality
`h` is the published `subgroup_eq_of_splitComponents F G hj hs`. Right
invariance of `μ` is the published
`quotientHaarMeasure_rightInvariant_of_splitComponents`. Centrality and the
split-torus property come from `hs`.

- `continuous_splitComponentL2RightAction` proves joint continuity of the
  published `splitComponentL2RightAction`.
- `splitComponentL2JointRightAction` and `splitComponentL2BoundedRightAction`
  are the jointly continuous and bounded-operator forms of that action.
  Their `_apply` lemmas hold by definition.
- `splitComponentL2IntegratedAction F G hi hj hs ν f hf` is the integrated
  action, with `splitComponentL2IntegratedAction_apply` giving
  `∫ g, f g • splitComponentL2RightAction F G hi hj hs g φ ∂ν`.
  `norm_splitComponentL2IntegratedAction_le` gives the bound
  `∫ g, ‖f g‖ ∂ν`.
- `splitComponentL2Equiv_integratedAction` proves that the published
  `splitComponentL2Equiv F G hj hs` intertwines
  `haarQuotientL2IntegratedAction`, for any splitting coordinates of `T`, with
  `splitComponentL2IntegratedAction`.

## Provenance and scope

The quotient follows Getz--Hahn (2.20)--(2.21). Every construction here is
internal: it conjugates the published positive-torus continuity and
integration constructions by the published `L²` equivalence. No literature
theorem is attributed to this module.

This module does not prove `ComparisonStatement`; it imports the published
proof through `GroupSchemeRestrictionQuotientL2`. It does not prove the
existence of split components, the injectivity or finite index of
`characterRestrict i`, unimodularity, finite volume, smooth-vector
realization, convolution identities, compactness, trace-class properties or
any spectral decomposition.
