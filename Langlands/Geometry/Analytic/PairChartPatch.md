# Pair charts of a pullback square and the patches they identify

Module `Langlands.Geometry.Analytic.PairChartPatch`, namespace
`Langlands.Analytic.SaturatedAtlasPresentation`. All objects live in the
localized analytic category `LocalizedCategory.{u, v, v}` over a complete
ultrametric normed field `K`.

## Purpose and provenance

This is an internal prerequisite for Task 7765
(`CompactPullbackActionContinuityStatement`). No literature statement is
transcribed. The mathematical content is the classical fact that, over
affinoid charts, a fibre product of analytic spaces is the affinoid space of
the completed tensor product of the chart algebras, so the part of a fibre
product lying over a pair of compatible charts is itself affinoid. In Lean
this is assembled from Library results only:

- `greatestChartPullback`, `greatestChartPullbackFst`, `greatestChartPullbackSnd`
  and `greatestChartPullback_localized_isPullback`
  (`SaturatedTopChartComparison`). They build the pullback of two complete
  strong maps between presentations with greatest charts as the small
  spectrum of the affinoid pushout algebra. Smallness of that spectrum is an
  explicit instance argument in the Library.
- `localizedTopTargetHomEquiv` (`TopChartSpectralTests`), which turns a
  localized arrow into a presentation with a greatest chart back into a
  complete strong map.
- `domainObj`, `domainι`, `domainRestrict`, `domainLift` (analytic domains as
  objects) and `domainPreimage` (`LocalizedDomainBaseChange`).

## Declarations

- `range_chart_subset_chartDomainFullChart S i j`: every chart of the chart
  domain `S.domain (S.chartDomain i)` has range inside the range of its
  retained full chart `chartDomainFullChart S i`. Since that full chart is
  surjective, the full chart is a greatest chart of the chart domain.
- `chartDomainStrong φ i j h`: for a localized arrow `φ : X ⟶ Y` mapping the
  chart domain of `i` into the chart domain of `j` (hypothesis `h`), the
  complete strong map between the chart-domain presentations whose
  localization is `domainRestrict _ _ φ h`
  (`localizationFunctor_map_chartDomainStrong`).
- `PairChartData f g` for a cospan `f : U ⟶ B`, `g : V ⟶ B`: a chart `left`
  of `U`, a chart `right` of `V` and a chart `base` of `B`, with `f` mapping
  the chart domain of `left` into that of `base` and `g` mapping the chart
  domain of `right` into that of `base`.
- For `c : PairChartData f g`:
  - `leftDomain`, `rightDomain`, `baseDomain`: the three chart domains.
  - `leftMap`, `rightMap`: the restrictions of `f` and `g` to these chart
    domains (`leftMap_comp`, `rightMap_comp` state the compatibility with the
    inclusions).
  - `leftTop`, `rightTop`: the bounded algebra maps from the base chart
    algebra to the left and right chart algebras, i.e. the pullbacks of
    `chartDomainStrong` at the full charts.
  - `algebra`: the Library's affinoid pushout
    `AffinoidPushout.algebra c.leftTop c.rightTop`. It is the closed quotient
    of the appended Tate presentation of the two chart algebras that
    identifies the two images of the base chart algebra. It is a bounded
    pushout into complete ultrametric targets, so it plays the role of the
    completed tensor product.
  - Assuming `Small.{v} (BanachSpectrum c.algebra)`: `obj`, the pair chart (the
    Library's `greatestChartPullback` of the two `chartDomainStrong` maps);
    its projections `fst`, `snd` to the left and right chart domains; and
    `isPullback : IsPullback c.fst c.snd c.leftMap c.rightMap`. The smallness
    instance is passed explicitly to the Library constructions, because
    instance synthesis does not find it through the definitional unfolding.
  - `patch p q` for arrows `p : P ⟶ U`, `q : P ⟶ V`: the analytic domain
    `domainPreimage p c.leftDomain ⊓ domainPreimage q c.rightDomain` of `P`.
    `mem_patch_iff` states that a point lies in it exactly when `p` maps it
    into the left chart domain and `q` maps it into the right chart domain.
  - `patchFst`, `patchSnd`: the restrictions of `p`, `q` to the patch.
  - Assuming `hP : IsPullback p q f g`: `patch_condition`, `toP` (the arrow
    from the pair chart to `P` given by the universal property of `P`),
    `toP_mem_patch` (its image lies in the patch), `toPatch` (the
    corestriction to the patch), `fromPatch` (the arrow from the patch to the
    pair chart given by the universal property of the pair chart), and
    `patchIso : localizationFunctor.obj c.obj ≅ domainObj P (c.patch p q)`
    with `hom = c.toPatch hP` and `inv = c.fromPatch hP`.

## Remarks on the proof

`patchIso` is a purely categorical consequence of the two pullback
properties: both composites are checked to be identities by `hom_ext` of the
relevant pullback, after cancelling the monomorphic domain inclusions
`domainι`. No pointwise argument through the projections is used. This
matters because Berkovich points of a fibre product are not determined by
their two projections, so the isomorphism of the pair chart with the patch
must come from the universal properties.
