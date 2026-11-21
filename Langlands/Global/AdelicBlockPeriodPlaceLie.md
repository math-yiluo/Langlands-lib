# Upper triangular place directions in the Lie algebra of a block period

`blockShapeRealLieDiagonal` extracts an ordered diagonal block in
actual archimedean matrix coordinates. Subtracting the sum of the
inserted diagonal blocks of an upper triangular matrix leaves a strict
upper block matrix. Extracting the diagonal block commutes with inserting
a matrix at a single real or complex place.

The real and complex place statements express this split in the actual
real Lie algebra of the block period. This allows the block period's
single-block differentiation formula and the vanishing on strict upper
blocks to be applied to the local upper triangular Lie identity.

`isUnnormalizedBlockLieEvaluation_real_of_period` and its complex
analogue use this split on a source acted on by the actual automorphic
operator algebra. A supplied formula for differentiating a single
Levi block and the vanishing of the strict upper block directions
imply the unnormalized place evaluation predicate.
