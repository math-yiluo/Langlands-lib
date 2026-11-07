# The canonical restriction split-centre quotient `[G]`

Author: Worker 112.

Getz--Hahn (2.20), printed p. 68 (`getz-hahn-2024-automorphic-representations`),
define `A_G` as the neutral component of the real points of the greatest
`ℚ`-split torus in the restriction of scalars `Res_{F/ℚ} Z_G`. Display (2.21),
p. 69, forms the quotient `[G] = A_G G(F) \ G(A_F)`.

The published module `AdelicRestrictionSplitCentre` builds this quotient as
`RestrictionSplitCentre.Quotient F G S j` for a supplied morphism
`j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`. The published
`AdelicRestrictionSplitCentreQuotient` gives it the measure
`quotientHaarMeasure F G S j`. Every published result about this quotient
takes `S` and `j` as parameters.

This module removes those parameters. It proves that every affine group scheme
locally of finite type over a field has a split component. It then fixes, once
and for all by choice, one split component of `Res_{F/ℚ} G` and one of `G`.
The resulting quotient `CanonicalQuotient F G` and measure
`canonicalMeasure F G` depend only on `F` and `G`.

"Canonical" here means "chosen once, with no further data". The choice is made
with `Classical.choose`. The independence section shows that every other split
component of the restriction gives literally the same subgroup. Its quotient
is identified with the chosen one by the identity on representatives, and this
identification preserves the measures and right translation.

**Relation to the source.** The chosen torus is a split component of
`Res_{F/ℚ} G` in the sense of the published `IsSplitComponent`: a central
split torus admitting no proper factorization through another central split
torus. Getz--Hahn use the greatest `ℚ`-split torus of `Res_{F/ℚ} Z_G`. This
module does not prove that the two agree. The subgroup is the published
`subgroup F G S j`, the image in `G(A_F)` of the positive real points of `S`.

## Data

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- From the Reductive section on, two hypotheses appear:
  - `hCST : CentralSplitTorusCharacterStatement.{0}`. This is the published
    proposition that, over every field, every nonzero rational character of
    a connected reductive group restricts nontrivially to some central split
    torus. It is unproved in the current Library; its proof is open task
    `4f432abe-c26e-45a1-97de-0f87624ccf5b`.
  - `hG : IsConnectedReductive G`.

## Existence of split components

Namespace `Langlands.GroupScheme`, any field `k`, any universe `u`.

- `cancel_of_isClosedSubgroup` (private): a closed subgroup
  `i : H ⟶ G` is a monomorphism, so `f ≫ i = g ≫ i` implies `f = g`. The proof
  applies `cancel_mono` to the underlying closed immersion.
- `exists_isSplitComponent`: every group scheme `G` over `Spec k` whose
  underlying scheme is affine and locally of finite type has a split
  component. No reductivity is assumed.

The proof takes the largest central split torus `j : B ⟶ G` from the published
`exists_largestCentralSplitTorus` (module `SplitComponentProof`). Its
finite-type hypothesis on the coordinate algebra comes from the published
`finiteType_coordinateAlgebra`. Suppose `f ≫ i' = j` with `i'` a central
split torus. Universality gives `g` with `g ≫ j = i'`. Cancelling the closed
subgroups `j` and `i'` shows that `f ≫ g` and `g ≫ f` are identities, so `f`
is an isomorphism. This repeats the first half of the published proof of
`splitComponentStatement`, which assumes connected reductivity. Here only
affineness and local finite type are used.

## The chosen split components

Namespace `Langlands.Global.RestrictionSplitCentre`.

- `canonicalRestrictionTorus F G` and `canonicalRestrictionComponent F G`:
  the source torus and the morphism of the chosen split component of
  `AffineWeil.groupScheme ℚ F G`, which is `Res_{F/ℚ} G`.
  `isSplitComponent_canonicalRestrictionComponent` records the defining
  property.
- `canonicalTorus F G` and `canonicalComponent F G`: the chosen split
  component of `G`. `isSplitComponent_canonicalComponent` records the
  defining property.

All of these come from `exists_isSplitComponent` by choice.

## The canonical quotient and measure

- `canonicalSubgroup F G` is the published `subgroup F G S₀ j₀` for the
  chosen restriction component `j₀ : S₀ ⟶ Res_{F/ℚ} G`.
- `canonicalRationalSubgroup F G` is the published `rationalSubgroup`: this
  subgroup joined with the principal points `G(F)`.
- `CanonicalQuotient F G` is the published `Quotient F G S₀ j₀`, that is,
  `[G] = A_G G(F) \ G(A_F)` as a left coset space.
- `canonicalMeasure F G` is the published `quotientHaarMeasure F G S₀ j₀`:
  the pushforward of the published norm-one quotient Haar measure. It needs
  no comparison or reductivity hypothesis.

Subgroup equalities. Each is derived from the published
`subgroup_eq_of_splitComponents`, which applies the published theorem
`comparison`.
- `canonicalSubgroup_eq_imageSubgroup`: the canonical subgroup equals the
  published positive image `imageSubgroup F T₀ G i₀` of the chosen split
  component of `G`.
- `subgroup_eq_canonicalSubgroup`: for every split component `j` of the
  restriction, `subgroup F G S j = canonicalSubgroup F G`.
- `imageSubgroup_eq_canonicalSubgroup`: for every split component `i` of `G`,
  `imageSubgroup F T G i = canonicalSubgroup F G`.
- `rationalSubgroup_eq_canonicalRationalSubgroup`: the same for the joins
  with the principal points.

## Independence of the choice

Let `j : S ⟶ Res_{F/ℚ} G` be any split component, with proof `hj`.

- `toCanonicalQuotient hj` is the published `congrSubgroupHomeomorph` for the
  equality above. It is a homeomorphism `Quotient F G S j ≃ₜ CanonicalQuotient F G`.
  It sends `[x]` to `[x]` (`toCanonicalQuotient_mk`) and commutes with right
  translation (`toCanonicalQuotient_rightTranslate`).
- `toCanonicalQuotientMeasurableEquiv hj` is the same map as an equivalence
  of the quotient sigma algebras. Its coercion is `toCanonicalQuotient hj`
  (`coe_toCanonicalQuotientMeasurableEquiv`).
- `measurePreserving_toCanonicalQuotient`: this map carries
  `quotientHaarMeasure F G S j` to `canonicalMeasure F G`. Both measures are
  pushforwards of the same norm-one measure. The map composed with
  `normOneToQuotient F G S j` is `normOneToQuotient F G S₀ j₀`, checked on
  representatives.

For any split component `i : T ⟶ G`:
- `positiveToCanonicalQuotient hs` is the published `quotientMeasurableEquiv`
  from the positive-torus quotient `PositiveRationalQuotient F G T i` to
  `CanonicalQuotient F G`.
- `measurePreserving_positiveToCanonicalQuotient`: it carries the published
  `positiveRationalQuotientHaarMeasure F G T i` to `canonicalMeasure F G`.

## Reductive groups

Assume `hCST` and `hG`.

- `canonical_characterRestrict_injective` (uses `hCST` and `hG`): restriction
  of rational characters along `canonicalComponent F G` is injective. This is
  the published `characterRestrict_injective_of_centralSplitTorusCharacter`.
- `canonical_finiteIndex` (uses only `hG`): its range has finite index. This
  is the published `characterRestrictionFiniteIndexStatement`.

The next results apply published lemmas from
`AdelicRestrictionSplitCentreQuotient` to the canonical data. They use
`canonicalSubgroup_eq_imageSubgroup`, the two results above, and the
centrality and splitness of the chosen component of `G`.
- `isClosed_canonicalRationalSubgroup`: `A_G G(F)` is closed in `G(A_F)`.
- `canonicalQuotient_t2Space`: `[G]` is Hausdorff.
- `canonicalQuotient_borelSpace`: the inherited quotient sigma algebra on
  `[G]` is the Borel sigma algebra.
- `canonicalSubgroupHaarMeasure F G hCST hG`: the full Haar measure on
  `A_G G(F)`. It is the published `subgroupHaarMeasure`, transported from the
  intrinsic positive-torus normalization of the chosen split component of
  `G`. The instance `canonicalSubgroupHaarMeasure_isMulRightInvariant` and
  the theorem `canonicalSubgroupHaarMeasure_isHaarMeasure` record its
  invariance and Haar property.
- `canonicalMeasure_isCompatible`: `canonicalMeasure F G` is Weil compatible
  (published `IsCompatible`) with the fixed Haar measure on `G(A_F)` and
  `canonicalSubgroupHaarMeasure`.
- `canonicalMeasure_rightInvariant`: `canonicalMeasure F G` is invariant under
  every right translation (published `QuotientRightInvariant`).
- `canonicalMeasure_isOpenPosMeasure`: `canonicalMeasure F G` is positive on
  nonempty open sets.

The last three need right invariance of Haar measure on the norm-one adelic
subgroup. Each proof supplies it locally from the published
`AdelicGroupPoints.normOneHaarRightInvariant`, using that `G` is smooth with
connected underlying space.

## L² spaces

- `canonicalL2Equiv F G` is the published `splitComponentL2Equiv` for the two
  chosen components. It is a linear isometric equivalence from the published
  `QuotientL2` of the positive-torus quotient of `canonicalComponent F G`
  onto `Lp ℂ 2 (canonicalMeasure F G)`.
- `canonicalL2RightAction F G hCST hG` is the published right regular
  representation `rationalQuotientL2RightAction` of `G(A_F)` on
  `L²([G])`, built from `canonicalMeasure_rightInvariant`.
- `canonicalL2Equiv_rightAction`: given any right-invariance proof for the
  positive-torus measure, `canonicalL2Equiv` intertwines the published
  `quotientL2RightAction` with `canonicalL2RightAction`.

For any split component `j` of the restriction:
- `toCanonicalL2Map hj` and `fromCanonicalL2Map hj` compose with the inverse
  of `toCanonicalQuotientMeasurableEquiv hj` and with that map itself, using
  Mathlib's `Lp.compMeasurePreservingₗᵢ`. They are mutually inverse
  (`fromCanonicalL2Map_toCanonicalL2Map`,
  `toCanonicalL2Map_fromCanonicalL2Map`).
- `toCanonicalL2Equiv hj` is the resulting linear isometric equivalence
  `Lp ℂ 2 (quotientHaarMeasure F G S j) ≃ₗᵢ[ℂ] Lp ℂ 2 (canonicalMeasure F G)`.
  `coeFn_toCanonicalL2Equiv` gives its almost-everywhere formula
  `q ↦ f (e⁻¹ q)`.
- `toCanonicalL2Equiv_rightAction`: given any right-invariance proofs for the
  two measures, the equivalence intertwines the two right regular
  representations `rationalQuotientL2RightAction`. The proof checks the
  underlying maps on representatives with `toCanonicalQuotient_rightTranslate`.

## Scope

The module proves no relation between split components of `Res_{F/ℚ} G` and
the greatest `ℚ`-split torus of `Res_{F/ℚ} Z_G`. Every reductive result above
depends on the unproved `CentralSplitTorusCharacterStatement`. Finite volume,
reduction theory and automorphic forms are not treated here.
