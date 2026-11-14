# An inverse-right eigenbasis for the supplied orthogonal cover

This internal construction uses the rational point in `StandardTorusTransport`.
The vector representation sends that point to an invertible matrix over the
original field. Its rows form a basis, obtained by mapping the standard basis
through the right-multiplication linear equivalence.

The comparison square is evaluated on every affine coefficient algebra.
`affineMatrix_constantPoint` identifies the conjugating matrix there with the
entrywise scalar extension of the original matrix. The standard orthogonal
torus has diagonal matrix with entries given by `torusWeights`. Consequently
the rows of the conjugating matrix are eigenvectors for the inverse-right
action, with eigenvalues the inverse diagonal entries, which are exactly the
negative standard vector characters pulled back along the comparison map.

`exists_inverseRight_eigenbasis` records this single basis and its identity
over every commutative coefficient algebra. The proof uses group inversion
and diagonal matrix multiplication; it retains finite fields and
characteristic two. The construction is derived internally from the published
matrix, character, and rational conjugacy interfaces and introduces no
additional mathematical premise.
