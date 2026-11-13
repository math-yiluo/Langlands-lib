# Discrete actual root-value differences for integer-valuation data

This internal helper ports the published `ActualAffineRootLocalFiniteness`
argument to an arbitrary field and the original explicit integer valuation.
It imports the preceding `IntegerAffineRootArrangement` helper and does not
supply local-field structure or change any apartment data.

Finite-index restriction of rational characters to the actual central split
torus gives a positive integer denominator for every character. After clearing
that denominator, the evaluation of every actual centralizer translation is an
integer: `IntegerValuation.eval_centralizerTranslation` identifies it with the
negative source-positive integer order of the actual rational-character value.
The construction and the sign use `IntegerValuation.order`, not a local-field
normalized valuation.

Two opposite-pair reflections for one relative root have a correction in the
actual centralizer, by the preceding arrangement helper. Full supplied V6
identifies that correction's original apartment action with translation. The
reflection formulas show that its root evaluation is twice the difference
of the original two root-value functionals. Thus every such difference becomes
integral after multiplication by twice the fixed positive denominator.

At any apartment point, bounded same-root functionals therefore inject into a
bounded set of integers. Affine maps with a fixed derivative are determined
by their value at that point; the integer bound gives a finite set of maps.
The finite actual relative-root set and the description of ordinary affine
roots as extended jump functionals give bounded finiteness of the original
ordinary affine roots. Together with the preceding finite spanning derivatives
and coroots, this constructs a locally finite reflection arrangement.

The declarations retain an explicit opposite-pair premise where inherited
from the local helper; the published rank-one factorization, via
`IntegerValuationBuildingData.hasOppositeFactorPairs`, supplies it for every
input bundle. No order-one-unit witness is used by discreteness. Fibre
infinitude and the full exact affine-root-system target remain for assembly.
