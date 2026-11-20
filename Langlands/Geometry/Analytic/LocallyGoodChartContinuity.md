# Continuity of analytic actions from local covers by good charts

Author: Worker 976.

This internal module turns the good-chart criterion of `GoodChartContinuity`
into a local form. The field `K : Type u` is complete, normed and ultrametric.
Analytic spaces lie in `LocalizedCategory.{u, v, v}`. The group `G : Type z`
carries an arbitrary topology.

- `IsGoodChart.of_cover`: let the underlying space of `X` be Hausdorff. Suppose
  a chart `W` lies in the union of the ranges of finitely many good charts.
  Then `W` is good, even when the covering charts do not lie inside `W`. Each
  intersection `W ∩ c` is compact, and the net property
  (`IsNet.exists_finite_cover_of_subset_inter`) covers it by finitely many
  charts inside `W ∩ c`. These are good by `IsGoodChart.of_subset`. They lie
  inside `W` and cover it, so `IsGoodChart.of_finite_cover` applies.
- `IsLocallyGood σ` says that, at every point `y` of the underlying space,
  `IsLocallyChartCovered (IsGoodChart σ) Set.univ y` holds. That predicate comes
  from the Library module `QuasiEtaleRigidity/RefinementGluing`. It asks for
  finitely many good charts containing `y` whose union contains a neighbourhood
  of `y`.
- `isContinuousAction_of_locallyGood`: on a Hausdorff underlying space, every
  locally good action satisfies `IsContinuousAction`. For a test triple on a
  chart `W`, compactness of `W` selects finitely many of the given
  neighbourhoods covering it. The corresponding finitely many good charts cover
  `W`, so `W` is good by `IsGoodChart.of_cover`. The Library's
  `isNear_id_of_spectralBound_preservedChartPullback` then gives the
  near-identity test. No compactness of the whole space is needed.

## Provenance and scope

This module is internal, a prerequisite for continuity on compact analytic
pullbacks (Task 7765). It is the interface with the geometric step of that
task. The geometric step must still show that the pullback action is locally
good.
