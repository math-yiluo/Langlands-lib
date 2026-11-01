# Coarse product-Levi reversal

This module contains the existing coarse reversal declarations extracted from
`Classification.OppositeCuspidalJacquetFiltrationProof`, with their names,
statements and implementations unchanged. They remain in the namespace
`Langlands.OppositeCuspidalJacquetFiltration`.

For any commutative ring `R` in an arbitrary universe and any block shape `C`,
`leviReverseEquiv C` reindexes the actual product Levi by `i ↦ i.rev`.
`leviReverseEquiv_apply` gives its coordinate formula. The theorem
`reverseMatrix_mul_leviEmbedding` identifies this reindexing with conjugation
by the block-reversal matrix, and `reverse_leviEmbedding_leviReverseEquiv`
expresses the same identity in the opposite direction. These declarations
include rank zero and require no representation-theoretic hypotheses.

The common module lets
[`OuterReversal`](OuterReversal.md) and the
[classification transfer proof](../Classification/OppositeCuspidalJacquetFiltrationProof.md)
reuse the same coordinate construction without importing either result into
the other. It adds no mathematical result.
