# Steinberg tensor embeddings from covariant exhaustion

`SteinbergTensorEmbeddingFromCovariantStatement` is the implication
`SteinbergCovariantExhaustionStatement → SteinbergTensorEmbeddingStatement`,
at the same universe `u`. The theorem
`steinbergTensorEmbedding_of_covariantExhaustion` proves it. It proves neither
proposition by itself.

## Proof

Let `k`, `p` and a simply connected `G` with affine total space be given, as in
`SteinbergTensorEmbeddingStatement`.

1. Simple connectedness includes semisimplicity and hence connected
   reductivity. The published field `isConnectedReductive.isAffineHom` makes
   the structure morphism of `G` affine, which is the instance the covariant
   statement requires.
2. The covariant statement supplies `Λ`, `j`, `H`, `H'`, `i`, `i'`, `χ`, `ψ` and
   its four conditions.
3. The same `Λ` and `j` are the witnesses for the embedding statement. For each
   finite right-stable subspace `V` with basis, whose elements are left
   `j`-invariant on all test schemes, the support theorem
   `Chevalley.exists_tensor_embedding_of_covariant_exhaustion` (in
   `CovariantTensorEmbedding`) produces the required `m`, `σ`, `π` and
   injective intertwiner, with `σ` rationally irreducible.

The two `IsAffine` instances on the total space of `G`, the one given by the
embedding statement and the one derived from the affine structure morphism,
agree because `IsAffine` is a proposition.

## Consequence

Composed with the published reduction
`simplyConnectedPositiveCharConjugationMap_of_steinberg`, this shows that
`SteinbergCovariantExhaustionStatement` implies the exact positive-characteristic
conjugation-map statement. That composite is not stated as a separate theorem
here, and the covariant proposition remains unproved.
