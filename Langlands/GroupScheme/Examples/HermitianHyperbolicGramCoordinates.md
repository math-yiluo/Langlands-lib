# Actual matrix coordinates for several hyperbolic planes

This internal linear algebra construction turns a `HyperbolicDecomposition`
into an actual invertible Gram congruence. It uses the original linear-first
pairing throughout. It does not assume that the remaining middle space is
anisotropic.

`MultiHyperbolic.productCoordinates` identifies functions on the three blocks
with the three coordinate families. `coordinateMatrix` is the actual invertible
matrix of a linear automorphism of a finite function space. Its Gram-congruence
entry is the full pairing of the corresponding images of standard basis vectors.

For a decomposition `d`, `functionCoordinates` expresses its coordinates as a
single function space. `middleGram` evaluates the original pairing on the
inverse images of middle standard basis vectors, with the indices ordered to
match the linear-first convention. Evaluating `d.pairing_eq` on inverse images
of all standard basis vectors gives exactly `MultiHyperbolic.gram d.middleGram`:
the two cross blocks are identity matrices and all other non-middle blocks
vanish.

If the original vector space is a finite function space, the decomposition's
dimension equality gives `indexEquiv`. The actual automorphism `basisCoordinates`
first relabels block coordinates and then returns to the original vectors.
`gram_congruence` proves that conjugating the original Gram matrix by its
invertible coordinate matrix gives the reindexed full block Gram matrix.

The proof uses elementary coordinate evaluation and the published hyperbolic
decomposition and diagonal-block definitions. It requires no classification or
split-rank comparison. This is an internal prerequisite for transporting actual
diagonal split subtori, and does not itself assert a group-scheme lower bound.
