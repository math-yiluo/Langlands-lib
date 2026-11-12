# Integral points of one affine étale chart have closed image

Authors: Worker 80 (proof draft), Worker 196 (checked against Library commit `68eafb81` and
submitted unchanged).

Proof of `Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianChartIntegralPointsClosedStatement.{u}`.
The entry theorem is `henselianChartIntegralPointsClosed`.

The target: let `K : Type u` be a nontrivially normed field whose closed unit ball is a subring
`O` (`∀ x, x ∈ O ↔ ‖x‖ ≤ 1`), with `HenselianLocalRing O`. Let `X` be a separated algebraic
space locally of finite type over `Spec O`, `U` a scheme over `Spec O` with `U.left` affine, and
`f : U → X` with `hom f` étale. Then the image of
`u ↦ (baseChangeRingPointsEquiv O K K X).symm (RingPoints.changeRing (Algebra.ofId O K)
(RingPoints.map f ((schemeRingPointsEquiv O U O).symm u)))` is closed for
`etaleChartTopology K X_K`, where `X_K = baseChange (Spec.algebraMap O K) X`.

## Route

`U(O)` is a closed subset `B` of `U_K(K)` on which every coordinate function of `U_K` is
bounded. The Library theorem `isClosed_preimage_image_of_bounded` (module
`EtaleChartTotallyDisconnected`) says that, over a henselian ultrametric field and for a
separated space, the image of such a set under an affine étale chart meets every other affine
chart in a closed set. Since every rational point lies in the image of an affine chart and chart
maps are open, the complement of the image is open.

## Declarations

Namespace `Langlands.AlgebraicGeometry.PointTopology.HenselianUnitBall`:

- `affineSchemePointEquiv_apply`: for `X` affine over `Spec R` and `p : X(S)`, the coordinate
  of `p` at a global section `a` is `(Scheme.ΓSpecIso S).hom (p.left.appTop a)`. Proof:
  `Spec.map_injective` and `affineSchemePointEquiv_spec`, as in the Library lemma
  `GroupScheme.affineSchemePointEquiv_evaluation`. It is elaborated with
  `set_option backward.isDefEq.respectTransparency false`.
- `isClosed_range_changeRing`: for `U` affine over `O`, the range of
  `RingPoint.changeRing (Algebra.ofId O K) : U(O) → U(K)` is closed for
  `schemePointTopology O U K`. In the affine topology it is the preimage of
  `⋂ₐ {φ | φ a ∈ closedBall 0 1}`: a `K`-point with all coordinates in `O` comes from the
  `O`-algebra map with values in `O`. This is the argument of the Library lemma
  `HenselianUnitBall.isOpen_range_changeRing`, with all coordinates instead of finitely many
  generators.
- `bounded_baseChange_range_changeRing`: every coordinate function `g` of
  `ringBaseChange O K U` is bounded on the image of `U(O)` under `ringPointBaseChangeEquiv`.
  The functions pulled back along `pullback.fst` generate the coordinate ring over `K`
  (`adjoin_range_baseChange_fst_eq_top`). On such a function the value at the image of
  `v ∈ U(O)` is the value of `v` itself (by `affineSchemePointEquiv_apply`,
  `ringPointBaseChangeEquiv_left_fst` and `Scheme.Hom.comp_appTop`), which lies in `O`, so has
  norm at most `1`. `bounded_of_adjoin_eq_top` propagates the bounds.

Namespace `Langlands.AlgebraicGeometry.AlgebraicSpace`:

- `henselianChartIntegralPointsClosed : HenselianChartIntegralPointsClosedStatement.{u}`.

## Proof of `henselianChartIntegralPointsClosed`

1. `K` is ultrametric (`HenselianUnitBall.isUltrametricDist`) and henselian as a valued field
   (`henselianIffValuationRingHenselian`). `X_K` is separated (`IsSeparated.baseChange`),
   quasi-separated (`SpaceProductPoints.isQuasiSeparated_of_isSeparated`,
   `IsQuasiSeparated.baseChange`) and locally of finite type (`HasAtlasProperty.baseChange`).
   `U` is locally of finite type over `O`
   (`HenselianIntegralPointsOpen.locallyOfFiniteType_of_isEtale`).
2. `U_K = ringBaseChange O K U` is affine, locally of finite type and quasi-compact over `K`, and
   the base-changed chart `restrictAtlas (Spec.algebraMap O K) (hom f)` is étale. This gives an
   affine `EtaleFiniteTypeChart` `c`, as in the Library proof of quasi-compactness
   (`HenselianIntegralPointsCompactProof`).
3. Let `B ⊆ U_K(K)` be the image of the range of `U(O) → U(K)` under the homeomorphism
   `ringPointBaseChangeEquiv O K K U` (`schemeBaseChangeTopology_proof`). It is closed by
   `isClosed_range_changeRing`, and bounded by `bounded_baseChange_range_changeRing`.
4. The set in the statement equals `c.pointMap '' B`: the chart map sends the image of `v` to
   the image of `f(v)` (`baseChangeRingPointsEquiv_schemePointsMap` and
   `RingPoints.changeRing_map`, as in the openness proof).
5. For `z` outside `c.pointMap '' B`, choose an affine chart `e` and `v` with `e.pointMap v = z`
   (`exists_affine_chart_pointMap_eq`). The preimage `e.pointMap ⁻¹' (c.pointMap '' B)` is
   closed (`isClosed_preimage_image_of_bounded`), so the image under `e.pointMap` of its
   complement is an open neighbourhood of `z` (`EtaleFiniteTypeChart.isOpenMap_pointMap`)
   disjoint from `c.pointMap '' B`.

The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Sources

The statement is derived (see its Markdown); the proof route is the author's, built from the
Library results named above.
