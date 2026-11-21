# The full kernel of a simply connected split even orthogonal cover

`splitCoverKernelIso` identifies the full scheme-theoretic kernel of a simply connected central cover of the split even orthogonal identity component. The split hyperbolic rank is at least three. The resulting scheme is the one-factor product of μ₂.

The actual standard maximal split torus lifts through the cover. Its cocharacter image has index two by the parity lattice calculation, and the full scheme kernel is therefore the diagonalizable group of the cyclic character group of order two. The explicit finite diagonalizable comparison gives the one-factor μ₂ model. In characteristic zero, `natCard_splitCoverKernel_points` computes exactly two points over the splitting field.

The comparison is derived from the Library's orthogonal coroot lattice and full index-two kernel theorem. It provides the degree of the vector cover in the scalar spin Hasse argument of Kneser, *Lectures on Galois Cohomology of Classical Groups*, §5.11, p. 99.
