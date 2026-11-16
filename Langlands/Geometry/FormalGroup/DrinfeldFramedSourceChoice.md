# Actual rational framing squares for changes of source-chart selection

This internal module proves compatibility of the actual normalized
framing with two refinements of the same reduced target whose finer
principal covers agree. The refinements may select different
original charts.

`refinedChartFraming_sourceChoice` composes the normalized framing
on the first finer chart with the actual rational route through
the two selected original charts and their formal transition.
The result is exactly the normalized framing on the second finer
chart. The proof cancels the intermediate actual refined-chart
inverse pair, reassociates the rational composition, and applies
`chartFraming_transition` on the selected original charts.

`refinedChartFraming_sourceIso` identifies that comparison route
with the evaluation of the existing specified actual
`orderSourceIso`. This is the source-choice formal isomorphism
used when joining different-cover comparisons. The result is
equality of entire actual full-order quasi-isogenies.

`sourceChoiceFramingSquare` packages the two normalized framings,
that evaluated specified source-choice isomorphism, the identity
on the actual globally extended fixed frame, and the proved
commuting equation. It supplies actual square data.

All local-field, division-algebra, embedded-subfield, residue-field,
height-certified fixed-frame, fixed-`Nilp` and universe hypotheses
of the framed representatives remain. Both refinements are of
the same reduced target; their equal finer covers may be
infinite.

The provenance is internal from the actual global framing
transition equation, refined-chart identifications and actual
source-choice isomorphisms. No equality of rational maps is
inferred from point equality. Compatibility with successive
refinement, direct-comparison composition, collapse of comparison
chains, varying-base functoriality and representability remain
separate.
