# Actual framing squares for successive principal-cover refinements

This internal module compares the actual normalized framing on a
direct composite principal refinement with the route through two
successive refinements.

`successiveRefinedFraming` starts at the globally extended fixed
frame, applies the existing normalized framing to a selected
intermediate chart, and then applies the inverse actual second
refined-chart identification. It is an actual full-order
quasi-isogeny into the tested successive-refinement chart.

`refinedChartFraming_comp` follows the direct refined framing
by the evaluation of the specified actual `orderCompIso`.
The result equals the successive route, as equality of entire
actual rational quasi-isogenies.

The proof uses `orderCompQuasi_chart` to compare the two routes
back to the selected original target chart. The actual inverse
equations identify the corresponding reversed routes. Both
framing constructions start from the same actual globally
normalized original-chart framing, so reassociation gives the
stated equality.

`successiveRefinementFramingSquare` packages these actual maps,
identity on the globally extended fixed frame, and the proved
equation as a `CommutingSquare`. It retains the actual
direct-to-successive formal comparison.

All local-field, central-division-algebra, embedded-subfield,
residue-field, height-certified fixed-frame, fixed-`Nilp` and
universe hypotheses of the actual framed representative remain.
The two successive principal covers may be infinite.

The provenance is internal from actual refinement composition,
its specified formal order isomorphism, normalized framing and
actual rational inverse equations. No equality of formal maps is
inferred from point equality. Refinement of general framed
comparisons, their direct composition, comparison-chain collapse,
varying-base functoriality, height statements for the successive
route and representability remain separate.
