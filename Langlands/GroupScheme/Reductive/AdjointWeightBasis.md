# Weight coordinates of the adjoint representation

These are derived coordinate comparisons for the actual adjoint representation
of an affine group scheme and the published representation weight spaces.
They use arbitrary affine test algebras, so the equations retain their
scheme-theoretic meaning over finite as well as infinite fields.

`mem_representationWeightSpace_iff_affine` specializes the representation
character-space equation to the torus of a split pinning.
`finrank_representationWeightSpace_eq_card` applies the character projector to
the basis expansion of each weight vector. The surviving basis vectors are
exactly those of the prescribed weight. Their linear independence supplies a
basis of the weight space.

`adjointBaseChangeWeightSpaceEquiv` restricts the pulled-back Lie-coordinate
equivalence to a weight space. Naturality of the coordinates extends the vector
to the test algebra. The base-change comparison for the adjoint action and the
representation matrix then identify the two eigenvector equations.

`exists_adjointBaseChangeWeightBasis` starts with the full character
decomposition of a split torus. Each root Lie weight space is a line by
`splitRootLieLine`. The coordinate comparison and the dimension count therefore
give a unique basis index at each root. Any basis index with nonzero weight
has a nonzero Lie weight space by the same comparison, so its weight belongs
to the actual root set and its index is among those already assigned.
