# The global degree-one comparison for tensoring by a line bundle

This internal derived unit works over any `S : Scheme.{u}`, with actual
module sheaves `M`, `N`, a natural number `n`, local freeness of `M` of rank
`n + 1`, and rank-one local freeness of `N`. Both projective schemes are
the genuine joint frame atlases already constructed from these hypotheses.
Write `F` for `atlasIso.hom`, from the tensor atlas to the source atlas,
and `p` for the tensor atlas's projection to `S`.

`sourceTensorTwistModule` is the actual module
`F* O_source(1) ⊗ p* N`. On each joint chart,
`sourceTensorTwistChartIso` tensors the existing source degree-one chart
comparison with the actual base-line trivialization and contracts the
structure-module factor. No global trivialization of `N` is assumed.

`sourceTensorTwistChartIso_restrict` proves that these contractions
restrict by the genuine tensor-atlas degree-one transition. It applies
the generic `tensorChartContractionIso_restrict` to the proved source
and base-line restriction laws. The resulting transition is the source
transition followed by multiplication by `dualLineProjectiveUnit`.
The existing `tensor_chartTwistIso` identifies this composite with the
tensor transition. `tensorTwistRestrictionIso` is the same transition
with its chart schemes explicit; `tensorTwistRestrictionIso_hom` states
the resulting equality of module morphisms.

`tensorLineTwistChartIso` composes the tensor-atlas standard chart
isomorphism with the inverse source tensor contraction. The helper
`chartComparison_restrict` shows that two local standard-form
comparisons with the same transition give a restriction-compatible
comparison between their domains. Its proof cancels the smaller
target comparison and uses functoriality and the two restriction laws.
This gives `tensorLineTwistChartIso_restrict`.

The joint basis is closed under intersections because joint frames and
line trivializations restrict to any smaller open. `FrameAtlas.restrictionIso`
therefore glues the local comparisons to `tensorLineTwistIso`, an
isomorphism of actual module sheaves

`O_tensor(1) ≅ F* O_source(1) ⊗ p* N`.

`tensorLineTwistIso_local` gives its forward map after pullback to
every joint chart. All restriction equations in the concrete application
are proved from the two local-freeness hypotheses; none are extra
compatibility assumptions.

The tensor factor in this global formula is on the pulled-back source
degree-one module. The older local definitions `tensorTwistChartIso`
and `twistChartIso` in `TensorLineTwistCharts` are not used as the
gluing family, and this unit makes no compatibility assertion for them.

The constructions and proofs derive from the published actual frame
atlases, the source and base-line restriction equations, the tensor
transition scalar formula, tensor contraction, and module gluing on an
intersection-closed frame atlas. No new literature assertion is used.
Transport to the fixed `FrameBundle`, the relative cubic embedding,
and the ordinary-moduli representability theorem remain further work.
