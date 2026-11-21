# Positive matrix size for automorphic functions

`exists_positiveMatrixEmbedding_of_isClosedSubgroup` supplies a positive-size
closed matrix embedding that preserves the given automorphy conditions.
When the given size is positive, the same representation works. In size
zero, injectivity on every test scheme makes every test-point group
trivial, because an invertible matrix of size zero is unique. The unit
section of the group scheme is then inverse to its map to the terminal
object over the base.

The trivial representation of size one is a closed immersion in this
case. Its underlying map is the isomorphism to the base followed by
the unit section of `GL₁`, which is a closed immersion over a field.
The only automorphy condition involving the representation is moderate
growth. The adelic group is trivial, so the value at its identity
gives an exponent-zero bound for the new embedding. The other
conditions are inherited directly.

This derived lemma handles the different matrix-size hypotheses of the
Library's Eisenstein continuation and functional-equation statements.
