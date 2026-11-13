# Generating weight bases from finite matrix algebra tori

Let K and L be arbitrary fields with a K-algebra structure on L. Supply a
finite K-basis of the full algebra of N by N matrices over L, and an actual
morphism from a standard split K-torus to its unit group. The definition
`weightColumn` is a column of one of the coefficient matrices of the inverse
universal unit, using `FiniteAlgebraTorusWeights.weightElement`.

If the morphism is a monomorphism of underlying schemes, `exists_weightBasis`
selects an L-basis of L^N from those columns. Each selected basis vector has
the integral character label of its projector. Those labels generate the
entire integral character lattice. Each coefficient projector acts on the
basis vector as the identity exactly when its label agrees, and as zero
otherwise.

The proof uses the complete orthogonal idempotent identities from
`FiniteAlgebraWeightIdempotents` and basis selection from `MatrixIdempotentBasis`.
Every nonzero projector label occurs among the selected basis labels.
Faithfulness gives integral generation by the full regular weight support;
its inclusion in the selected labels therefore gives integral generation
by the selected labels too. This argument uses no infinite-field or
characteristic assumption.

This is internal derived infrastructure for the Hermitian split-rank upper
comparison. The pairing and its invariance are not assumed here, and no
orthogonality of Hermitian pairings is asserted in this module.
