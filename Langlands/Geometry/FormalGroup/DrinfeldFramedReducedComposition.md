# Composition of actual reduced framing comparisons

This module composes framing squares for specified comparisons of the
reduced targets of actual framed formal atlases.

`globalFrameQuasiIso_trans` proves that the fixed-frame identifications forced by
successive residue-map equalities compose. The proof destructs the representatives
and equalities, then applies the rational identity law. The mapped version
`globalFrameQuasiIso_map_trans` follows by actual coefficient extension, its
composition law and its compatibility with rationalizing integral isomorphisms.

For two reduced-target comparisons `c` and `d` whose middle finer covers are
equal, `reducedComparisonOnChart_join` identifies the evaluated map of their
specified join with the first evaluated comparison, the evaluated actual middle
`orderSourceIso`, and the second evaluated comparison. The selected source charts
are transported along the stored cover equalities. Extensionality reduces this
whole quasi-isogeny equation to the forward full-order tensor Hom equation;
rationalization of the two actual integral compositions proves that equation.
The stored inverse is then determined by the forward map.

`ReducedFramingSquare.join` assumes the reduced framing squares for `c` and `d`
and proves the reduced framing square for this exact join and the composite
residue-map equality. On each defined finer test chart, the middle representative's
`refinedChartFraming_sourceIso` identifies its two normalized framings through the
actual source-choice map. Associativity pastes this identity with the second
input square. The actual `square_paste` identity then combines the result with
the first input square. The two preceding composition identities identify the
resulting right edge with the prescribed joined coordinate map and the left edge
with the prescribed composite fixed-frame identification.

`ReducedFramingSquare.trans` applies the existing refinement theorem to the
actual `commonLeft` and `commonRight` product-cover refinements and then joins
the results. This is exactly the specified `BasicAtlas.OrderAction.Comparison.trans`,
including its integral coordinate map and refinements.

`composedReducedFramingSquare` retains this result as actual `CommutingSquare`
data. Its top and bottom are the normalized framings of the first and final
representatives on the composite comparison's selected charts. Its right edge
is `reducedComparisonOnChart (c.trans d)`, and its left edge is the coefficient
extension of `globalFrameIso (e.trans f)`. Its commuting equation is the preceding
transitivity result.

All declarations retain the supplied nonarchimedean local field, finite-dimensional
central division algebra, embedded subfield, coefficient ring, residue field,
height-certified fixed frame, inherited test universes and one fixed Nilp object.
Principal covers may differ and may be infinite. Each input comparison is an
actual comparison of the reduced targets; its whole rational framing square is
an explicit premise. No equality of formal maps is inferred from point equality.

This is derived internal content from `DrinfeldFramedComparison`,
`DrinfeldFramedReducedRefinement`, `DrinfeldFramedSourceChoice`,
`DrinfeldFramedComparisonIdentity`, `AtlasOrderComparisonEquivalence` and the
actual full-order quasi-isogeny calculus. It asserts no new external-literature
theorem. Compatibility of quotient reduction with refinement and composition of
original target comparisons, original `FramingSquare` transitivity, direct framed
`Comparison.trans`, comparison-chain collapse, varying-base functoriality, actions
and representability remain separate.
