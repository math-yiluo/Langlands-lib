# Common real determinant twists of binary normalized products

Author: Worker 103.

`T.binaryNormalizedProductRealTwistIso A B s` constructs an actual smooth
isomorphism from `ν^s (A × B)` to `(ν^s A) × (ν^s B)`, where `ν^s` is the
published `T.segmentFactor` and the product is the literal all-rank
`T.binaryNormalizedProductFunctor`. The factors have carrier universe `uV`
and the output has carrier universe `max uF uV`; the two universes are
independent. The supplied field topology is used throughout.

For two positive ranks, the proof uses the published identification with the
binary block shape, applies `T.normalizedProductDeterminantTwistEquiv` to the
smooth scalar character `a ↦ |a|^s`, and identifies the two twisted block
families by their explicit two indices.

If the first rank vanishes, the published `binaryLeftZeroTensorEquiv` identifies
the actual product with the tensor model on which only the second factor acts,
after the equality reindexing of the ambient group. The identity linear map
intertwines its total twist with the tensor model of the twisted factors:
the determinant character is unchanged by the equality reindexing and the
scalar moves to the second tensor factor. The right-zero proof uses the first
tensor factor in the same way. These proofs include the case where both ranks
are zero; the rank-zero carrier is retained as a tensor factor.

The provenance is internal: the module composes the published common-character
twist construction for normalized induction with the explicit all-rank binary
models. It adds no irreducibility, admissibility, finite-length or unitarity
hypothesis and does not assert those properties.
