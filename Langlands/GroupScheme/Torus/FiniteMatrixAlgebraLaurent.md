# Laurent matrices and their projector eigenvectors

This internal helper identifies K[M] tensor the full matrix algebra over L
with matrices over L[M], for arbitrary fields K and L, a K-algebra structure
on L, and an additive commutative monoid M. The construction moves the tensor
product through matrices, swaps coefficient factors, and applies Mathlib's
scalar extension equivalence for monoid algebras. A monomial tensor a matrix
maps entrywise to the same monomial with the matrix entry as coefficient.

For an actual split-torus morphism into the finite matrix algebra unit group,
`inverseUniversalMatrix` is its inverse universal unit in these Laurent
matrix coordinates. Its finite monomial expansion has the coefficient
projectors from `FiniteAlgebraWeightIdempotents`. The projector eigenvector
rule therefore implies the exact Laurent eigenvector equation on any vector
whose weight occurs in the support. Every vector in a basis of projector
columns has such an occurring label, since a label outside the support would
make that basis vector zero.

The proof uses the published tensor/matrix comparison and Mathlib's monoid
algebra scalar extension equivalence, then transfers the previously proved
finite universal expansion. Matrix multiplication of monomials and finite
sums establishes the action formula. No Hermitian invariance is asserted in
this module; it supplies the coordinate algebra needed to prove it later.
