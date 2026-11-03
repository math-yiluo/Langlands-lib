# Fixed-vector vanishing for the actual norm-one Galois lattices

This proof establishes the published
`Langlands.GroupScheme.WeilGm.normOneGaloisFixedLatticesStatement`, with its
finite-dimensionality, separability, coefficient normality and explicit
minimal-polynomial splitting premises unchanged.

For two embeddings into the coefficient field, their field ranges are
isomorphic by composing the inverse of the first range equivalence with the
second. Mathlib's `AlgEquiv.liftNormal` extends this isomorphism to an
automorphism of the normal coefficient field. Its commuting identity gives
transitivity of postcomposition on the embeddings. This does not require a
specified algebra structure from the extension field to the coefficient field.

An integer function fixed under inverse pullback has equal values at any two
embeddings: evaluate fixedness at the image of an embedding under an
automorphism supplied by transitivity. Thus the function is constant.
The embedding set is finite, and splitting and separability give nonemptiness
by the published `separableEmbedding_nonempty`. The coordinate sum of a
constant function is its value multiplied by the positive cardinality.
Consequently a constant sum-zero function vanishes.

For a fixed quotient class, choose an arbitrary representative. Equality of
its class with each permuted class says their difference lies in the
diagonal, so this difference is constant. The permutation preserves the sum,
which makes the sum of that constant difference zero. Nonemptiness and
integer cancellation force the difference itself to vanish. The representative
is therefore invariant, hence constant by transitivity, and its quotient class
is zero. In particular, representative invariance is proved from class
invariance rather than assumed.

Finally the two published additive equivalences
`normOneSeparableEmbeddingCocharacterEquiv` and
`normOneSeparableEmbeddingCharacterEquiv`, together with their ordinary Galois
equivariance identities, transfer these coordinate conclusions to actual
cocharacters and actual characters of the base-changed norm-one group scheme.
The converse directions follow from linearity of the four actions at zero.

The provenance is internal: this is the elementary fixed-vector argument
isolated by the published statement, using its actual norm-one comparisons
and Mathlib's normal-extension lifting, finite sums, and submodule quotient
identities. It asserts no rational descent or anisotropy result.
