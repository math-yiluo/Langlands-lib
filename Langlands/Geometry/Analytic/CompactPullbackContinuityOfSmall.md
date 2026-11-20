# Continuity on compact analytic pullbacks under pair-chart smallness

Module `Langlands.Geometry.Analytic.CompactPullbackContinuityOfSmall`,
namespace `Langlands.Analytic.SaturatedAtlasPresentation`.

## Purpose and provenance

This module assembles the Task 7765 development into the target
proposition `CompactPullbackActionContinuityStatement`
(`CompactPullbackActionContinuity`). It proves the target under one extra
hypothesis, and proves it unconditionally whenever the field universe is at
most the space universe (`UnivLE.{u, v}`), in particular when both are the
same universe. No literature statement is transcribed. The
mathematical content is in the imported modules:

- `PairChartPatch` and `AffinoidPatchPullback` (Worker 931): pair charts, i.e.
  affinoid fibre products of charts, identified with patches of the pullback.
- `PairChartConvergence` (Worker 931): spectral convergence of the action on
  pair charts, and eventual preservation of patches.
- `PairChartCover` (Worker 931): every point of the pullback is locally
  covered by charts inside pair-chart patches.
- `AffinoidPatchGoodCharts` (Worker 976): charts inside an affinoid patch
  with converging pullbacks are good charts.
- `GoodChartContinuity` and `LocallyGoodChartContinuity` (Worker 976): on a
  Hausdorff space, local covers by good charts give `IsContinuousAction`.

## The smallness hypothesis

`AffinoidSpectraSmall.{u, v} K` is the proposition
`∀ R : PresentedAffinoidAlgebra K, Small.{v} (BanachSpectrum R)`. It says
that the Berkovich spectrum of every presented affinoid algebra over `K` is
small in the space universe `v`. The proof needs it only to make each pair
chart, the small spectrum of an affinoid pushout algebra, an object of
`LocalizedCategory.{u, v, v}`. The Library's `greatestChartPullback` takes the same
smallness, as an instance argument for its pushout algebra. It holds automatically whenever `UnivLE.{u, v}`
(`affinoidSpectraSmall_of_univLE`, via Mathlib's instance `UnivLE.small`),
in particular when `u = v`. Whether the target holds without it
in general universes is the open question in operator request
`a87ede08952355398eb14c6ddc2957c0`. The hypothesis is option (a) proposed
there.

## Declarations

- `AffinoidSpectraSmall.{u, v} K` (definition, a proposition): the smallness
  hypothesis above.
- `affinoidSpectraSmall_of_univLE [UnivLE.{u, v}] : AffinoidSpectraSmall.{u, v} K`.
- `isLocallyGood_of_pullback_of_small hS hP hU hV hp hq : IsLocallyGood σ`.
  Here `hP : IsPullback p q f g`, `σU` and `σV` are continuous, and `p`, `q`
  are equivariant. The proof applies `isLocallyChartCovered_of_pairCharts`
  with `Q := IsGoodChart σ`. For a chart `W` inside the patch of a pair
  chart `c`, it applies `isGoodChart_of_affinoidPatch` to
  `c.eventually_preimage_patch` and `c.spectralConvergesOn_patchPullback`.
  The smallness instance for `c.algebra` comes from `hS`.
- `compactPullbackActionContinuity_of_small hS`: the body of
  `CompactPullbackActionContinuityStatement`, verbatim, under `hS`. The
  Hausdorff property of `P` is the second component of `IsCompactSpace P`.
  The theorem then applies `isContinuousAction_of_locallyGood` to the
  previous result. Compactness of `B`, `U`, `V` and `P` is not otherwise
  used.
- `compactPullbackActionContinuityStatement_of_univLE [UnivLE.{u, v}] :
  CompactPullbackActionContinuityStatement.{u, v, z}`: the target statement,
  with no extra hypothesis, whenever the field universe is at most the space
  universe. Worker 976 suggested this form of the corollary.
- `compactPullbackActionContinuityStatement_of_univ_eq :
  CompactPullbackActionContinuityStatement.{u, u, z}`: the special case of
  equal universes.
