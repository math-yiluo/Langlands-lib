# Fixed pinned chart transitions and canonical comparison naturality

This internal adapter uses the actual chart constructions of
`Reductive/GlobalPinningTransitions` and concerns supplied coherent root
frames; their existence is not proved here.

Let `G` be reductive over an arbitrary scheme `S`, with a closed split
fibrewise maximal torus, a supplied full global coordinate root datum
`P`, a chosen base, and supplied frames of all actual root weight modules
on all affine tests. Assume the frame vectors commute with coefficient
extension in the precise original-group dual-number-point sense of
`AffineRootFrames.IsCoherent`.

For two affine tests of `S` and any common scheme mapping to them over
`S`, `affineFrameFixedComparison` packages the actual original-group
pullback transition as a fixed pinned comparison for the identity full
root-datum equivalence. Its underlying isomorphism is exactly
`affineFrameComparison`. The published identity formula for the fixed
torus map converts the exact normalized torus square into the fixed
torus predicate. The supplied frame coherence gives equality of the
identically labelled simple pinning points on every affine coefficient
test.

Now let `H` have the same geometric setup, with its own coordinate torus,
full root datum `Q`, base and coherent frames. Supply one full root-datum
equivalence `Q → P` matching the chosen bases, and the exact affine pinned
Isomorphism Theorem as an explicit proposition premise.
`canonicalAffineFrameComparison_naturality` proves that the square of
canonical fixed comparisons between `G` and `H` commutes with both
original-group chart transitions, on every common scheme. The proof
composes fixed comparisons along each side, simplifies the identity
root-datum equivalences, and applies fixed-comparison uniqueness on the
whole common scheme.

Neither the base nor the common scheme is assumed affine, connected or
quasi-compact. The two chart source schemes are affine. The result is an
internal composition of actual chart-transition preservation and fixed
pinned comparison uniqueness. It does not construct the frames, prove
the affine pinned theorem, or assert the isomorphism statement
`ReductiveSplitTorusBorelIsomorphismStatement`.
