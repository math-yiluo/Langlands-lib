# Actual fixed-frame and target chart comparisons over a new Nilp base

This module constructs actual full-order test-chart comparisons for the
implemented framed Nilp-base extension. It uses the actual quotient-cover
square and the supplied-target coefficient chart comparisons. It asserts no new
source theorem or representability result.

`onChart_ofIso` identifies rationalization followed by restriction with
rationalization of the actual chart isomorphism. `onChart_isoTransport` follows
the two actual composition equations and retains the source inverse, given
original chart map and target chart isomorphism in that order. This generic
transport-chart formula shares the coefficient-ring and rational-field
universe, as does the preceding atlas height-transport construction.

`baseChangeExtendedChart` transports the new reduced-target chart index through
the actual quotient-square cover equality. `baseChangeOriginalChart` then uses
the original reduced atlas's existing selected source for that extended image
generator. The unit theorem supplies its actual invertibility on the restricted
test algebra. These constructions do not choose another original chart.

`baseChangeTargetChartIso` first applies the actual target quotient-square
comparison on that chart, then the supplied-target coefficient comparison. Its
target is the same selected original target chart with the test-ring scalar
structure transported to the new one. Both formal maps and inverse equations
are retained.

`baseChangeFrameChartIso` follows the actual source maps used in the extended
framing: inverse global normalization for the new frame, inverse chart map of
`quotientFrameBaseChangeIso`, the original source coefficient-chart comparison,
and scalar transport of the original global normalization. It is an actual
formal full-order isomorphism from the new globally extended fixed frame on the
test to the scalar-transported original globally extended fixed frame.
It may depend on the specified chart through the constructed source maps; no
independence or canonical-source assertion is made here.

The parameters retain the local field, finite-dimensional central division
algebra, embedded field, coefficient and residue fields, fixed height-certified
frame and Nilp objects in universes `{v,u}`. Covers may be infinite and scalar
maps may merge generators. The normalized framing equation and preservation of
framing squares under base extension are outside this module; they are
`chartFraming_baseChange` in `DrinfeldFramedBaseChangeNormalization` and
`framingSquare_baseChange` in `DrinfeldFramedComparisonBaseChange`.
