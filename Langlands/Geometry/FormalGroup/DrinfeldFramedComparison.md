# Actual framing squares on reduced principal refinements

This internal interface equips an actual formal comparison of two
`DrinfeldFramedAtlas` representatives with a rational framing square.
All assumptions and universe restrictions of those representatives remain:
the supplied local field, central division algebra, certified embedded
unramified subfield, residue field and height-certified fixed frame are
unchanged. The two representatives lie over the same actual `Nilp` object.
Their covers may differ and may be infinite.

`globalFrame` extends the fixed special module along the stored residue map
before restricting it to any cover. `globalFrameIso` uses equality of two
residue maps to construct the identity formal coordinate comparison between
these extensions. It supplies no choice of a frame automorphism.

`refinedChartFraming` expresses the original full-order rational framing from
this global extended frame to a test chart of any actual refinement of the
reduced target atlas. It composes the inverse global-chart isomorphism, the
original framing on the selected old chart, and the inverse refined-chart
isomorphism. All three factors are actual full-order quasi-isogenies, so both
formal inverse equations are retained. Test algebras use the reduced
coefficient universe. `refinedChartFraming_height_zero` transports the
original local kernel-rank height presentations by these same two formal
isomorphisms. It preserves both rank exponents, their signed difference, and
the local scalar denominator exponents.

`reducedComparisonOnChart` evaluates the specified actual formal comparison
as a full-order quasi-isogeny on the two finer test charts.
`ReducedFramingSquare` requires equality of actual full-order quasi-isogenies on
every defined test chart of the right refinement of the reduced target
comparison. The left route applies the normalized first framing and then
the reduced comparison. The right route uses the identity frame comparison
forced by residue-map equality and then the normalized second framing.
The two original target covers need not agree: the specified target
comparison supplies actual refinements with equal finer covers, and its
quotient reduction supplies the refinements used in this equation.
`FramingSquare` applies this condition to that actual quotient reduction.

`Comparison` stores the actual target comparison, the equality of residue
maps and this square. Its target and reduced-target natural isomorphisms
are induced by those specified formal comparisons. An arbitrary
equivalence of point functors is not an input.

The provenance is internal. This combines the previously defined framed
representatives, global and refined formal chart comparisons, actual
quotient reduction of a full-order comparison, and local kernel-rank
height transport. It defines a comparison interface and proves the
normalized height condition. Reflexivity, symmetry, transitivity, a
framed quotient, descent, varying-base functoriality, actions and
representability remain separate obligations. It asserts no completeness
of the global tensor rational interface for all locally rational maps.
