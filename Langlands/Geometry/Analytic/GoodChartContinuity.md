# Continuity of analytic actions from a finite cover by good charts

This internal module gives a sufficient criterion for the Library's Berkovich
continuity `IsContinuousAction` (module `ContinuousAnalyticAction`). The field
`K : Type u` is complete, normed and ultrametric. Analytic spaces lie in
`LocalizedCategory.{u, v, v}`. The group `G : Type z` carries an arbitrary
topology; no topological-group structure is assumed.

## Chart-level facts

- `domainMap_comp_domainInclusion`: for nested analytic domains `D ≤ E` of a
  saturated presentation `S`, `S.domainMap h ≫ S.domainInclusion E` equals
  `S.domainInclusion D` as strong maps. The proof uses `ext_of_saturated` and
  checks that every local pullback is an identity restriction.
- `exists_restriction_comap_eq_aux`: a point of a chart lying in a smaller
  chart comes from the smaller chart's spectrum through the atlas restriction.
- `chart_comap_preservedChartPullback`: suppose an endomorphism `φ : X ⟶ X`
  satisfies `φ⁻¹(U) = U` for a chart `U`. The Library's
  `preservedChartPullback U φ` is the pullback of the restriction of `φ` to `U`.
  Its spectrum map, followed by the chart map, is `φ` on the underlying space.
  The proof applies the chart equation of the unique strong representative of
  `φ` restricted to `U` (`localizedTopTargetHomEquiv`). It then identifies that
  representative's base map with the restriction of `φ`.
- `restriction_comp_preservedChartPullback`: let `k ⊆ i` be charts, both
  satisfying `φ⁻¹(chart) = chart`. Then
  `restriction k i ∘ preservedChartPullback i φ` equals
  `preservedChartPullback k φ ∘ restriction k i`. The two strong representatives
  intertwine the strong domain inclusion. This follows by injectivity of
  `localizedTopTargetHomEquiv` and cancellation of the monic domain inclusion.
  Then `pullbackAtTop_comp` computes both sides. The pullback of the strong
  domain inclusion is the atlas restriction.

## Good charts

`IsGoodChart σ c`, for `σ : G →* Aut X` and a chart index `c` of
`presentationOf X`, is the conjunction of two conditions.

1. Eventually near `1 : G`, the underlying map of `σ g` satisfies
   `(σ g)⁻¹(chart c) = chart c`.
2. For every section `a` of the chart algebra,
   `SpectralConvergesOn (𝓝 1) (fun g => preservedChartPullback c (σ g).hom) id a`.
   Thus, for every `ε > 0`, eventually every spectrum point `x` satisfies
   `x (pullback(a) - a) ≤ ε`.

- `IsGoodChart.of_subset`: every subchart `k` of a good chart `c` is good.
  The atlas restriction makes `k` a full represented domain of the algebra of
  `c` (Library `restrictionDomain`). Preservation of `k` follows from
  `Domain.eventually_comap_mem_locus_iff` on the algebra of `c`, together with
  `chart_comap_preservedChartPullback`. Points outside `c` stay outside by
  preservation of `c`. Convergence on `k` follows from
  `Domain.spectralConvergesOn_of_factor`. The restriction naturality supplies
  the required factorizations.
- `IsGoodChart.of_finite_cover`: a chart `W` covered by finitely many good
  subcharts is good. Preservation of `W` is the union of the preservations.
  For the bound, every point of `W` comes from a point of some subchart, and
  restriction naturality reduces to that subchart.
- `isContinuousAction_of_goodCharts`: let the underlying space of `X` be
  Hausdorff. Suppose finitely many good charts cover it. Then `σ` satisfies
  `IsContinuousAction`. For a test triple on a chart `W` and each covering
  chart `c`, the intersection `W ∩ c` is compact. By the net property
  (`IsNet.exists_finite_cover_of_subset_inter`) it is covered by finitely many
  charts inside `W ∩ c`. These are good by `of_subset`, so `W` is good by
  `of_finite_cover`. The Library's
  `isNear_id_of_spectralBound_preservedChartPullback` then converts
  preservation and the spectral bound into `IsNear τ (σ g) 1`.

## Provenance and scope

This module is internal, a prerequisite for continuity on compact analytic
pullbacks (`CompactPullbackActionContinuitySmallStatement`). No source statement is transcribed. The criterion uses
only chart preservation and spectral displacement on finitely many charts. It
does not by itself provide such charts for any particular space.
