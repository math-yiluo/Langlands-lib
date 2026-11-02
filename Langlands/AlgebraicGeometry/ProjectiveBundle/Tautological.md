# Degree-one line bundle on the projective frame bundle

For a scheme `S`, an actual module sheaf `M` locally free of rank `n + 1`,
and any natural number `n`, this module constructs the line bundle
`FrameBundle.twistOne hM` on the already constructed projective scheme
`frameBundle M n hM`. The local pieces are the actual relative degree-one
line bundles on its projective charts. The construction works in an arbitrary
common scheme universe and does not require an affine or finite base cover.

`frameIntersection` and `frameTripleIntersection` are frame-bearing intersections
of base opens. The charts above an intersection have exactly the intersection of
the two global chart ranges. Since the chart maps are open immersions,
`isPullback_intersection` proves that the intersection chart is a genuine
scheme pullback. Its canonical comparison `intersectionIso` has the stated
projection formulas. Two successive applications of this pullback property give
`exists_tripleChartLift`: three chart maps agreeing in the global scheme lift to
one triple-intersection chart.

`chartTwistIso` uses the published coherent degree-one comparison for the
coordinate cocycle obtained from the chosen dual frames. On an actual pairwise
scheme pullback, `overlapTwistIso` normalizes both pulled-back chart twists to
the twist on the intersection chart, then composes one normalization with the
inverse of the other. These are actual module-sheaf isomorphisms, with no
supplied overlap or descended-line-bundle premise.

The proof of `overlapTwistIso_normalize` refines that normalization to any
smaller common frame chart, using `RefinedPullbackComparison.transition_normalize`
and the composition law for `chartTwistIso`. To prove
`overlapTwistIso_cocycle`, the three maps on a commuting triple-overlap diagram
are lifted to a common triple-intersection chart. Each of the six morphisms
in the descent equation preserves normalization to the same pulled-back twist.
The three canonical square comparisons have this property by
`CommonSourceCocycle.square_normalize`. Cancellation of the final invertible
normalization proves the equality. The equality is packaged by the published
`OpenCoverModuleGluing.CompEq4`, whose arguments are the six actual morphisms.
This wrapper allows the kernel to compare them separately during specialization.

The explicit chart cover `chartCover` has the same chart schemes and maps as
the existing frame-bundle cover. Specializing the commuting-diagram cocycle to
the canonical triple scheme pullbacks proves the full cover descent condition,
including repeated indices. `twistGluingData` supplies that proved condition to
`LineBundleGluingData.glue`, which yields `twistOne`. `twistOnePullbackIso` and
`twistOneModuleIso` identify its pullback with each chart's degree-one twist.
`twistOneModuleIso_compatible` proves that the chosen chart comparisons realize
the specified overlap identifications via the canonical pullback comparisons.

This is a derived construction from the published frame scheme, actual relative
degree-one twists, canonical module pullback coherence, common-refinement
comparisons and open-cover line-bundle gluing. It introduces no external-source
assertion. It does not prove frame-choice independence, tensor-line invariance,
a relative cubic embedding or ordinary moduli representability; those are
remaining parts of the host task.
