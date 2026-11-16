# Actual preservation of reduced framing squares under further refinement

This internal module proves that a specified
`ReducedFramingSquare` remains a framing square after any
further principal refinement of the specified comparison's
left finer atlas. The right further refinement is the exact
retargeting along its stored equality of finer covers.

`refinedChartFraming_comp_to_old` follows the direct refined
framing by the actual direct-to-successive comparison and the
refined-chart identification back to the selected original
finer chart. The result equals the original framing there.
Its proof uses the successive-refinement framing equation
and cancels the target inverse pair.

`ReducedFramingSquare.refine` uses the actual coordinate
`refinementChartSquare`. After postcomposing with its
invertible right comparison route, it applies that
commuting equation, the two preceding framing identities,
and the original framing square. Cancellation of that
actual right quasi-isogeny proves equality of the entire
new framing routes.

`refinedReducedFramingSquare` retains all four actual maps
of this refined square and the proved equation as actual
`CommutingSquare` data. Its top and bottom are the normalized
framings on the actual composite refinements; its right map
is precisely the evaluated refined coordinate isomorphism;
its left map is the fixed-frame identity forced by the
original residue-map equality.

All local-field, central-division-algebra, embedded-subfield,
residue-field, height-certified fixed-frame, fixed-`Nilp` and
universe hypotheses remain. Covers may differ and may be
infinite. The input is a specified actual comparison of the
reduced targets with its rational framing square.

The provenance is internal from actual rational restriction,
comparison-refinement and successive-framing squares.
No equality of formal maps is inferred from point equality.
This file does not yet prove that reducing a further-refined
original target comparison gives this same specified refined
reduced comparison. Original `FramingSquare` refinement,
direct-comparison composition, comparison-chain collapse,
varying-base functoriality and representability remain
separate.
