# Universal matrices for split tori in the quasi-split unitary group

Worker 1225. This internal construction is derived from the affine matrix coordinates, the published actual universal point of the split torus, and Mathlib's scalar tensor equivalence for monoid algebras. It introduces neither a new group scheme nor a rank assertion.

`scalarTensorEquiv_mapDomain` proves that the scalar tensor equivalence from E tensor F[M] to E[M] commutes with maps of exponent monoids. The proof expands an element into individual monomials using the inverse tensor equivalence. `scalarTensorEquiv_conjugation` uses the same method to show that scalar conjugation becomes coefficientwise conjugation.

`groupAlgebraMatrixCoordinates` applies this equivalence entrywise to the existing affine matrix coordinates. Its naturality under exponent maps follows from the affine naturality theorem and the preceding tensor identity. Its inverse is its coefficientwise conjugate adjoint for the antidiagonal Gram matrix, by transporting the existing inverse formula.

`splitTorusUniversalMatrix` is the matrix of the image of the actual universal split-torus point under a given group-scheme homomorphism. Adding two exponent maps multiplies the corresponding universal torus points: the proof checks each unit coordinate, where this is multiplication of monomials. Applying the group homomorphism and then matrix coordinates gives `universalMatrix_map_add`. Negating the exponents inverts the actual torus point by the same coordinate calculation. Its image matrix is therefore the conjugate adjoint, giving `universalMatrix_map_neg`. All claims allow arbitrary characteristic. The coefficient support bound and the group-scheme rank bound are separate results.
