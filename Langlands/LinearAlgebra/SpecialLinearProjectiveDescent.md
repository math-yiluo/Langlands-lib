# Descent of a projectively fixed conjugating matrix

Author: Worker 239.

This internal unit works with invertible matrices over arbitrary fields,
in every characteristic, and a finite matrix index type.
`normalizeEntry X p q hpq` divides `X` by its specified nonzero
`(p,q)` entry. The selected entry becomes one; it need not be on the
diagonal. Scalar centrality shows that the matrix has the same
conjugation action after every homomorphism to a commutative ring.

Two matrices having equal conjugation actions on `SL` differ by a unit
scalar. If both have their `(p,q)` entry equal to one, this scalar is one.
It follows that if every automorphism of a specified subgroup preserves
the action of `X` on `SL`, then every automorphism fixes
`normalizeEntry X p q hpq` exactly.

Whenever fixed coefficients lie in the image of a field embedding,
an exactly fixed invertible matrix descends along that embedding.
Choose preimages of all its entries. Their determinant is nonzero
because its image is the determinant of the original invertible matrix.
Thus the chosen matrix is invertible over the smaller field.
For a nonempty index type an invertible matrix has a nonzero entry, so
normalization followed by this coefficient descent gives a descended
matrix whose image is a scalar multiple of the original matrix.

For an embedding `f : L →ₐ[K] M` with `M/K` finite Galois, the fixed
field theorem identifies the coefficients fixed by
`f.fieldRange.fixingSubgroup` with the image of `f`. This supplies the
coefficient descent hypothesis in the preceding construction.

Finally, a matrix over `L` whose image under a field embedding is a
unit scalar matrix is itself a unit scalar matrix: recover the scalar
from any diagonal entry and use injectivity of coefficient mapping.

All arguments are derived from the imported scalar centralizer,
scalar-conjugation and Galois fixed-field theorems. This unit assumes
projective invariance; it does not construct an outer action or a
quadratic extension, or assert the final Hermitian presentation.
