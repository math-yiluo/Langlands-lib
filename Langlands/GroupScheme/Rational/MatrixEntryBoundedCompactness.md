# Compactness from uniform matrix-entry bounds

This internal proof establishes
`Langlands.GroupScheme.MatrixEntryBoundedCompactnessStatement` without changing
its hypotheses.

First, `MatrixRepresentation.rationalMatrix_eq_pointHomeomorph` identifies the
actual rational matrix with the composite of the canonical rational/affine
point homeomorphism and the published general linear point homeomorphism.
The comparison is checked on each matrix entry using regular-function
evaluation. Consequently, `isClosedEmbedding_rationalMatrix` transports the
published closed-immersion theorem for canonical rational points to the
actual matrix unit group.

For the closing proof, choose the scalar bound from
`HasUniformlyBoundedEntries`. A finite product of compact scalar closed balls
is a compact set `K` of matrices. The closed embedding `Units.embedProduct`
records a matrix and its inverse in a product with the opposite matrix
monoid. Both lie in the corresponding compact product: the first uses the
given bound, and the second applies the same bound to the inverse group point
and uses that `rationalMatrix` is a group homomorphism. The composite closed
embedding therefore has compact preimage containing every rational point.

Finally, every global regular-function evaluation is continuous in the
canonical rational-point topology, through the published affine point
homeomorphisms. Its compact image has a nonzero scalar valuative bound by
`IsCompact.exists_valuative_bound`, proving algebraic boundedness.

The argument includes dimension zero and both local-field characteristics.
It uses neither reductivity nor a finite-type assumption, and leaves the
spectral and anisotropy inputs to the host theorem open.
