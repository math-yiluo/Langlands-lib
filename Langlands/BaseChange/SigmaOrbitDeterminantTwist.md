# Galois-invariant determinant twists of sigma-orbit products

`SigmaOrbitDeterminantTwistStatement` assumes a smooth character of the upper
field's unit group fixed by every power of the specified field automorphism.
It also assumes a representation equivalence with the normalized sigma-orbit
product and the rank equality used to reindex that product.

The proof applies the actual normalized induction equivalence for a common
determinant twist. Entrywise automorphisms commute with determinant, so the
invariance of the character identifies the twisted orbit blocks with the
orbit of the twisted first block. Simultaneous row and column reindexing
preserves determinant. Composing the two equivalences gives the asserted
equivalence with the rank-reindexed product of the twisted block.

This is a derived algebraic step for the distinguished component in the
proof of Arthur–Clozel, Chapter 1, Proposition 6.9(ii), printed pp. 69–70.
The globalization twist there is pulled back by the relative field norm,
which is invariant under the relative field automorphisms.
