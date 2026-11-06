# Proof that the adelic spread topology of an affine scheme is the affine topology

Authors: Worker 105, Worker 1525.

`Langlands.Global.adelicSpreadAffineTopology` proves exactly
`Langlands.Global.AdelicSpreadAffineTopologyStatement` (from
`Langlands/Global/AdelicSpreadAffineTopologyStatement.lean`) at an arbitrary universe `u`. It
is the pair of `curvePlaceSpreadAffineTopology` (proving
`CurvePlaceSpreadAffineTopologyStatement`) and `numberFieldSpreadAffineTopology` (proving
`NumberFieldSpreadAffineTopologyStatement`).

The two clauses keep the target's hypotheses. In the function-field clause, `k` is a perfect
field and `F` a function field over `k` with the compatible `RatFunc k`-algebra structure. In
the number-field clause, `K` is any number field and the base is Mathlib's `S`-integers. In
both clauses `S` is an arbitrary finite set of places, and `X` is a scheme over the
`S`-integers whose structure morphism is locally of finite type and quasi-compact. `Y` is an
affine scheme over the field, and `e` is an arbitrary isomorphism from the generic fibre of
`X` to `Y`. The conclusion is that the spread topology on `Y(A_F)` equals the affine point
topology on `RingPoint`, which is the evaluation topology of Conrad's Proposition 2.1.
Conrad states this at the start of Section 4 (printed p.9) of *Weil and Grothendieck
approaches to adelic points* (December 31, 2011), registered as
`conrad-2011-weil-grothendieck-adelic-points`, and in its abstract.

The proof follows the same route in both characteristics. The lemma names below are given in
the function-field form `curvePlace…`; each has a number-field counterpart `numberField…`
with the same proof.

## A general topology lemma

`iSup_coinduced_eq_of_isOpenMap`: let `φ_i : Z_i → Y` be maps from topological spaces into a
topological space `Y`. Suppose each `φ_i` is continuous and open and every point of `Y` is in
the image of some `φ_i`. Then the final topology `⨆ i, coinduced φ_i` is the given topology of
`Y`. Continuity gives one inequality. For the other, a set `V` open in the final topology is
the union of the images `φ_i '' (φ_i ⁻¹' V)`, because the maps cover `Y`. These images are
open because the maps are open.

## Affine models

Here `X` is a model over the `S`-integers with `X.left` affine. Each lemma assumes only the
hypotheses listed.

- `curvePlaceFixedModelStageTopology_eq_affine` (`X` affine): the topology on the points of
  `X` with values in a level `A_{F,T}`, `T ⊇ S`, is the affine topology. By definition the
  stage topology is induced from the level topology of the base change of `X` to the
  `T`-integers. That base change is affine (instances `instSpreadAffineCurveBaseChange` and
  `instSpreadAffineBaseChange`), so its level topology is the affine topology by the
  published `curvePlaceLevelModelPointTopology_eq_affine` and
  `numberFieldLevelModelPointTopology_eq_affine`. The base-change point equivalence is a
  homeomorphism of affine topologies by the published
  `isHomeomorph_ringPointBaseChangeEquiv`, so the induced topology is the affine topology.
- `curvePlaceAdeleLevelOverι_isOpenEmbedding`: the inclusion of each level into the full
  adeles is an open embedding, because the level is open (published `isOpen_curvePlaceAdeleLevel`
  and `isOpen_numberFieldAdeleLevel`).
- `curvePlaceFixedModelStage_isOpenEmbedding` (`X` affine and locally of finite type): each
  stage map `X(A_{F,T}) → X(A_F)`, the literal `RingPoint.changeRing` along the level
  inclusion, is an open embedding for the affine topologies, by the published
  `affineSchemeCoefficientOpen_proof`.
- `curvePlaceFixedModelAdelePointTopology_eq_affine` (`X` affine, locally of finite type and
  locally of finite presentation): the fixed-model topology on `X(A_F)` is by definition the
  final topology of the stage maps. By the two previous items the stage maps are continuous
  and open for the affine topology on `X(A_F)`. They cover `X(A_F)` by the
  local-finite-presentation clause of the published
  `curvePlaceFixedModelPointComparisonProperties` and
  `numberFieldFixedModelPointComparisonProperties`. The general topology lemma then gives the
  affine topology.
- `curvePlaceSpreadAdelePointEquiv_isHomeomorph` (`X` and `Y` affine): the spread point
  identification `X(A_F) ≃ Y(A_F)` is a homeomorphism of affine topologies. It equals the
  base-change point equivalence followed by postcomposition with `e`. The first map is a
  homeomorphism by `isHomeomorph_ringPointBaseChangeEquiv`. The second is the published
  homeomorphism `affineSchemePointIsoHomeomorph`; the generic fibre is affine by
  `ringBaseChange_isAffine`.
- `curvePlaceSpreadAdelePointTopology_eq_affine_of_isAffine` (`X` affine, locally of finite
  type and locally of finite presentation, `Y` affine): the spread topology is by definition
  transported from the fixed-model topology along the spread point identification. By the two
  previous items it is the affine topology.

## Affine space and the general case

`curvePlacePolynomialModel k F S n` is affine `n`-space over the `S`-integers, the spectrum
of the polynomial ring in `n` variables. `curvePlacePolynomialGenericFiberIso` identifies its
generic fibre with affine `n`-space over the field. It composes the published spectrum
base-change isomorphism `ringBaseChangeSpectrumIso` with the spectrum maps of Mathlib's
`MvPolynomial.algebraTensorAlgEquiv` and its inverse. The instances
`instSpreadAffineCurvePolyLFT`, `instSpreadAffineCurvePolyLFP`, `instSpreadAffineCurvePolyQC`
and their number-field counterparts record that the polynomial model is locally of finite
type, locally of finite presentation and quasi-compact. Hence the affine case applies to it.

`exists_closedImmersion_affineSpace`: an affine scheme `Y` over a field `k` that is locally
of finite type over `k` has a closed immersion into affine `n`-space over `k` for some `n`.
Its coordinate ring is a finitely generated `k`-algebra, so it is a quotient of a polynomial
ring (`Algebra.FiniteType.iff_quotient_mvPolynomial''`). The closed immersion is the
canonical isomorphism of `Y` with the spectrum of its coordinate ring, followed by the
spectrum of the surjection (`IsClosedImmersion.spec_of_surjective`).

`curvePlaceSpreadAffineTopology` and `numberFieldSpreadAffineTopology` treat a general model
`X` of `Y` (locally of finite type and quasi-compact, not necessarily affine or finitely
presented):

1. The generic fibre of `X` is locally of finite type over the field, as a base change of
   `X`. Since `e` is an isomorphism over the field, `Y` is locally of finite type too.
2. Choose a closed immersion `g` of `Y` into affine `n`-space over the field.
3. The published `curvePlaceSpreadClosedImmersion` and `numberFieldSpreadClosedImmersion`
   allow independent models of source and target. Applied with the given model `X` and `e`
   for `Y`, and the polynomial model over the same `S` with its generic-fibre isomorphism for
   affine space, they show that `p ↦ p ≫ g` is a closed embedding from the spread topology on
   `Y(A_F)` to the spread topology on the points of affine space.
4. The latter spread topology is the affine topology, by
   `curvePlaceSpreadAdelePointTopology_eq_affine_of_isAffine`. So the spread topology on
   `Y(A_F)` is induced from the affine topology along `p ↦ p ≫ g`.
5. The affine topology on `Y(A_F)` is induced along the same map, by the published
   `isEmbedding_affineSchemePointMap`. The two topologies are therefore equal.

`adelicSpreadAffineTopology` is the conjunction of the two cases. The proof uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.
