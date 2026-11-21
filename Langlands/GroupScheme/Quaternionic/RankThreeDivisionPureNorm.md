# Pure norms of isotropic rank-three division forms

Worker 863, Task 7498.

Let a central quaternion division algebra over a characteristic-zero field
be extended to a field over which it remains a domain. Give the extension its
finite-dimensional division-ring structure and use the extended standard
conjugation `τ`. Suppose two is invertible and an invertible skew Gram matrix
of size three has a nonzero isotropic vector in its row pairing.

`exists_pureNorm_eq_matrixReducedNorm_of_isotropic` represents the Gram norm
by a quaternion in the alternating subspace of `τ`. Use the rank-three orthogonal
basis with two opposite nonzero diagonal values to put the matrix in the form
`diag(a, -a, b)`. The third value is nonzero by separation and belongs to the
alternating subspace. For the basis matrix `P`, the norm identity is
`N(H) N(P)^2 = N(a)^2 N(b)`. Multiplying `b` by the scalar `N(a) / N(P)` therefore
produces the required representative.

This is the division-place calculation in Springer, appendix to M. Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), Theorem 5.3.3(i),
printed p. 109 (PDF p. 115).
