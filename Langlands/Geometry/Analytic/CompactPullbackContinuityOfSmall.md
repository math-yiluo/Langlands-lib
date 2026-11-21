# Continuity on compact analytic pullbacks with small affinoid spectra

The theorem `Langlands.Analytic.SaturatedAtlasPresentation.compactPullbackActionContinuity_of_small`
in `Langlands.Geometry.Analytic.CompactPullbackContinuityOfSmall` proves
`CompactPullbackActionContinuitySmallStatement` from
`Langlands.Geometry.Analytic.CompactPullbackActionContinuitySmall`. This is the
assembly of the internal chart argument developed for Task 7765.

## Statement proved

Let `K : Type u` be a complete ultrametric normed field and `G : Type z` a
group with a topology. Assume that the spectrum of every presented affinoid
algebra over `K` is `v`-small. Consider a categorical pullback `P` of
`U → B ← V` in `LocalizedCategory.{u,v,v}`, with all four spaces compact
and Hausdorff. Suppose that `G` acts by analytic automorphisms on `P`, `U`
and `V`, the two projections are equivariant as analytic arrows, and both
factor actions are continuous in the Library's Berkovich test-triple sense.
The theorem proves `IsContinuousAction` for the supplied action on `P`.

The field, space and group universes are independent. The smallness
hypothesis is explicit; it is not a universe inequality. The local argument
uses it only to realize each pair chart, the spectrum of an affinoid pushout,
as an object in the same localized category. `AffinoidSpectraSmall.{u,v} K`
packages this hypothesis for the helper theorem below. It is definitionally
the leading premise of the statement. Both `affinoidSpectraSmall_of_univLE`
and the statement module's `small_banachSpectrum_of_univLE` furnish the
hypothesis if `[UnivLE.{u,v}]` is available, in particular if `u = v`.

## Implemented proof

1. **Cover by pair-chart patches.** `PairChartCover` gives a finite cover of a
   neighbourhood of each point of `P` by charts lying inside patches of the
   form `p⁻¹(Uᵢ) ∩ q⁻¹(Vⱼ)`, with `Uᵢ` and `Vⱼ` lying over a common
   chart of `B`. This cover uses the commutativity of the supplied square.
2. **Realize the patch affinoidly.** For each such pair, `hS c.algebra`
   supplies smallness of the spectrum of the completed affinoid pushout.
   `PairChartPatch` identifies the resulting localized pair-chart object with
   the analytic domain of `P` cut out by the two chart preimages, using the
   categorical pullback universal properties. This is `PairChartData.patchIso`.
3. **Control the action on the model.** `PairChartConvergence` gives eventual
   preservation of the patch near the identity and spectral convergence of the
   induced pullbacks on the pair chart. The factor actions control the two
   blocks of coordinates by equivariance of the full projection arrows.
   `AffinoidPushout.spectralConvergesOn_of_factors` extends the estimates to
   the whole pushout by finite polynomial approximation.
4. **Pass to the original charts.** `isGoodChart_of_affinoidPatch` in
   `AffinoidPatchGoodCharts` transfers preservation and spectral convergence to
   any chart of `P` contained in the patch, by representing it as an affinoid
   domain of the model. Applying this argument to the cover of step 1 gives
   `IsLocallyGood σ` via `isLocallyGood_of_pullback_of_small`.
5. **Verify the tests.** The main theorem extracts Hausdorffness of `P` from
   `IsCompactSpace P` and applies `isContinuousAction_of_locallyGood`. This
   criterion takes a finite subcover of the compact chart of each test triple,
   obtains goodness of that chart from the finite cover, and then uses its
   eventual preservation and spectral bound to give `IsNear` for that test at
   the identity. The proof does not otherwise use compactness of the four spaces.

There is no topological-group instance or action on `B`, no quasi-étale or
additional lifting or uniqueness premise, and no description of pullback
points as pairs. The two existing `UnivLE` and equal-universe corollaries
specialize the theorem after supplying smallness; neither proves the
superseded proposition at independent universes without that hypothesis.
