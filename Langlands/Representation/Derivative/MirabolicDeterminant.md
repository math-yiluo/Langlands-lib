# Determinants of the actual block-sum and mirabolic embeddings

These three elementary lemmas are extracted unchanged from Worker 593's
published `PartialDerivativeJacquetNormalization` module. Their namespace
`Langlands.Derivative.JacquetNormalization`, declaration names, hypotheses
and proofs are preserved. Both derivative normalization modules import this
shared pair.

For any commutative ring and all natural ranks, `determinant_blockSum`
computes the determinant of the actual block sum as the product of the two
determinants. Its proof uses simultaneous matrix reindexing and the
block-triangular determinant formula. `determinant_levi` specializes the
second block to the scalar identity, and `determinant_successor` applies
that identity to the actual mirabolic subgroup inclusion.

This relocation adds no mathematical result or hypothesis. It isolates the
existing matrix identities from the derivative-iteration and Jacquet
comparison imports, allowing the left-Phi scalar calculation to reuse them.
