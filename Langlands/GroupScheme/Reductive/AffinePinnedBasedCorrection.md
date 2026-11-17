# Affine etale charts with actual based inner correction

For any affine pinned models `M`, `N`, any common scheme `T` with base maps
`f`, `g`, and any actual comparison `e`, the construction
`affineBasedCorrectionChart e x` supplies an affine etale chart
`q : Spec A ⟶ T` above every point `x`. It supplies an actual section `c`
of the target group over `Spec A`, together with a `BasedCoordinateIso`
whose group isomorphism is exactly
`pullComparison e q ≪≫ (N.groupOver (q ≫ g)).innerIso c`.
Thus the corrected comparison has a full based root equivalence, preserves
the simple supports and standard coordinate pairings, and satisfies the
character formula on every relative test scheme.

`HasBasedCorrection` expresses the existence of this target section and based
data. `AffineBasedCorrectionChart` records the ring, map, etaleness, a point
above `x`, the section and the based data with the exact group-isomorphism
equality. `affineBasedCorrectionCover` assembles the selected charts into an
affine etale cover indexed by the points of `T`.
`AffineBasedCorrectionChart.preservesCocharacter` gives the exact canonical
ambient positive-coroot cocharacter equality for the corrected comparison.

This is an internal deduction from
`AffinePinnedSimultaneousNormalization` and `AffinePinnedAffineAlignment`:

1. `basedCorrection_pullComparison_comp_iff` proves invariance under the
   direct-versus-iterated normalized pullback identification. Its proof uses
   `pullComparisonAlong` with the explicit endpoint reassociations and its
   tower coherence theorem; it retains the actual comparison maps.
2. `exists_affine_etale_basedCorrection` starts from the existing etale
   Borel-and-torus normalization cover. Above a chosen point of one chart,
   `affineBasedAlignment` supplies an affine open refinement with based data
   for the corrected comparison. Pulling the original target section back
   with `pullBasePoint`, the theorems `pullComparison_trans` and
   `pullComparison_inner` identify that data's group isomorphism with the
   iterated original comparison followed by the pulled-back inner
   correction. The preceding coherence lemma expresses the result using the
   direct total chart map. An open immersion followed by an etale map is
   etale, and the two chosen point equalities prove coverage.
3. Classical choice packages the existence theorem as the chart construction.
   Its point and image equality give the covering condition. The existing
   `BasedCoordinateIso.cocharacter_comp` theorem gives the cocharacter claim.

There are no additional hypotheses on the supplied comparison or on the
common scheme. In particular, the scheme may be disconnected, nonaffine,
empty or not quasi-compact; the point-indexed cover of an empty scheme is
empty. The chosen based root equivalence may vary between charts. These
charts do not yet align the pinning vectors, so this module alone does not
prove `FppfLocalPinnedNormalizationExistenceStatement` or the parent
comparison-existence statement.
