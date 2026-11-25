# Proof that the Frobenius-twisted strong map does not extend to `F₄`

`nonExtension` proves [`NonExtensionStatement`](NonExtensionStatement.md): no
`StrongHom` between the `F₄`-extensions of the source and target presentations
retains every pair of charts admissible for `weakMap` with its ground-field
extended pullback. The statement does not prescribe the new base map.
This is an internal counterexample. All declarations are in the namespace
`Langlands.Analytic.GroundFieldExtensionCounterexample`.

Write `ι` for the inclusions `targetInclusion` and `sourceInclusion`, `ι_L` for
`PresentedAffinoidAlgebra.GroundFieldExtension.iota`, and `map` for the extension
of bounded algebra homomorphisms.

## Three target charts

- `leftIndex` is the selected chart `ofChart (upperChart (idempotent 3))` with
  locus `leftDomain`.
- `rightIndex` is `ofChart (upperChart (idempotent 2))` with locus
  `rightDomain`.
- `pointIndex` is `ofChart (upperChart (1 - idempotent 0))` with locus
  `pointDomain 0`.

`targetPoint_mem_upperChart_iff` shows that `targetPoint p` lies in the locus of
`upperChart (idempotent q)` exactly when `p ≠ q`. Hence
`not_leftDomain_subset_rightDomain` (witness `targetPoint 2`) and
`not_rightDomain_subset_leftDomain` (witness `targetPoint 3`). These show that the
two triple charts are selected; `pointIndex` is selected by
`isSelected_of_subset_pointDomain`.

- `admissible_leftIndex` and `admissible_rightIndex`: both triple charts are
  admissible for `weakMap`.
- `pointIndex_subset_leftIndex` and `pointIndex_subset_rightIndex`: the point
  chart lies in both.
- `weakPullback_comp_baseMap_left`: on the left chart, the pullback of `weakMap`
  composed with the chart's base map is `restrictMap`.
  `weakPullback_comp_baseMap_right`: on the right chart it is
  `frobenius.comp restrictMap`. They come from the general
  `weakPullback_comp_baseMap_of_not_subset` and
  `weakPullback_comp_baseMap_of_subset`.

## A point of the extended source and a test element

- `extendedEvaluation` is the bounded `F₄`-algebra map from the extended source
  algebra to `F₄` given by the universal property (`lift`) of the
  `F₂`-evaluation `sourceEvaluation 0` at the first factor.
- `extendedPoint` is the corresponding point. Its value at `s` is
  `‖extendedEvaluation s‖` (`extendedPoint_apply`).
  `spectrumProjection_extendedPoint` shows that it projects to `sourcePoint 0`.
- `comap_restrictMap_sourcePoint_mem`: the image of `sourcePoint 0` lies in
  `pointDomain 0`.
- `card_F₂` and `card_F₄` compute the field sizes `2` and `4`.
  `exists_pow_card_ne` gives `ω ∈ F₄` with `ω ^ 2 ≠ ω`: an element outside
  `{0, 1}`, which exists because `F₄` has four elements.
- `testElement ω = ι_L (ι (Pi.single 0 ω)) - ω • ι_L (ι (idempotent 0))`.
  `extendedEvaluation_test` computes `extendedEvaluation (map restrictMap
  (testElement ω)) = ω - ω = 0`. `extendedEvaluation_frobenius_test` computes
  `extendedEvaluation (map frobenius (map restrictMap (testElement ω))) =
  ω ^ 2 - ω`. Both use `map_iota`, `lift_iota` and the chart lemmas of
  `Charts`.

## The main argument

`exists_point_of_extends`: let `F` be a strong map between the extended
presentations. Suppose that on an admissible target chart `j` containing
`pointIndex`, `F` has the extended pullback `map (weakMap.pullback i j)`. Then
there is a point `w` of the extended `pointIndex` chart with two properties.
First, its chart image is `F.baseMap` of the chart image of `extendedPoint`.
Second, `w (map B₀ t) = extendedPoint (map (weakMap.pullback i j ∘ B_j) t)` for
every `t`, where `B₀` and `B_j` are the rational base maps of the two charts.

1. Let `u` be `extendedPoint` pulled back along `map (weakMap.pullback i j)`.
   By naturality of the spectrum projection, `u` projects to the pullback of
   `sourcePoint 0`. By `weakMap.chart_comm`, the original chart `j` sends this
   projected point to `weakMap.baseMap (sourcePoint 0)` in `pointDomain 0`.
2. By `IndexedAffinoidAtlas.GroundFieldExtension.mem_range_restriction_iff`,
   `u` is the pullback of a point `w` along the extended restriction from `j`
   to `pointIndex`.
3. The atlas law `restriction_chart` and `F.chart_comm` identify the chart image
   of `w` with `F.baseMap` of the image of `extendedPoint`.
4. `RationalSpectrumAtlas.restriction_comp_baseMap` and `map_comp` give the
   formula for `w`.

`nonExtension`: apply this to `leftIndex` and to `rightIndex`. Both resulting
points have the same image under the extended `pointIndex` chart embedding
(`isEmbedding_chart`), so they are equal. Comparing their formulas at
`testElement ω`, with `weakPullback_comp_baseMap_left`,
`weakPullback_comp_baseMap_right` and `map_comp`, gives
`‖ω - ω‖ = ‖ω ^ 2 - ω‖`. The left side is `0` and the right side is nonzero,
a contradiction.
