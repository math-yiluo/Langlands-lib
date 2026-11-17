# Finite covariant coefficient families

Worker 525. This is a derived supporting construction for the invariant
unit-ideal argument. It uses the finite stable covariant families and
scalar-preimage interfaces developed by Worker 690. It assumes no geometric
reductivity and proves no quotient affineness or independent reductivity theorem.

Work over a field k with group schemes H and J over Spec k and a homomorphism
iH from H to J. All functions below are actual global sections on J, and
covariance and right invariance are asserted on every relative scheme test,
including nonaffine and nonreduced tests. The family and coordinate index types
are finite and may be empty.

`blockFamily` extends a row on one summand of a finite direct sum by zero on
the other summands. `familyLinearMap_blockFamily` recovers the original linear
combination. `isRightCovariantFamily_blockFamily` proves covariance for the
direct-sum representation by expanding its block diagonal point matrix.

`isRightCovariantFamily_weighted` says that multiplying each covariant row by
an invariant section and summing preserves covariance for their common
representation. The proof applies invariance and covariance on the same
arbitrary test and exchanges the two finite sums.
`familyLinearMap_weighted` exchanges a linear combination with the invariant
weighted row sum; this identity itself needs no invariance assumption.

`exists_scalar_covariant_rows` assumes k is algebraically closed, H is smooth,
and the global section algebra A of J is nontrivial. Given invariant weights
s_i, covariant rows f_i for a common representation, and a vector v with
sum_i s_i * familyLinearMap(f_i)(v) = 1, it constructs a finite representation
sigma, covariant rows g_i and a vector c over k such that
sum_i s_i * g_i,j = algebraMap(c_j) for each j, c is nonzero, and c is fixed
by the actual dual representation of sigma on all tests.

The proof forms the weighted family w_j = sum_i s_i*f_i,j. In the coordinate
space of w it takes the inverse image U of the ground-field scalar subspace
of A. Right translation preserves scalars, so the published rational stability
criterion, applied using smoothness of H, makes U an actual stable subspace.
Split coordinates B,C for U restrict the common representation and every row.
The restricted weighted columns lie in the scalar subspace and therefore give
c. The original vector belongs to U because its weighted image is 1; its
restricted coordinates still evaluate to 1, so c cannot vanish. The existing
scalar-image fixed-vector theorem proves that c is dual-fixed.

`exists_scalar_covariant_coefficients` additionally assumes that J is affine
and starts with arbitrary coefficients a_i and sum_i s_i*a_i = 1. For each
a_i, finite stable-family existence in the whole section space supplies a
covariant family and a vector representing a_i. Their finite direct sum and
block rows give the input for the previous theorem. Nontriviality of A follows
by evaluation at the identity point of J into the nontrivial global section
ring of Spec k. The conclusion is the same scalar covariant coefficient
family, with no additional nontriviality premise.

The provenance is internal: these are finite-sum and subspace constructions
using the Library direct-sum, stable-coordinate and scalar-image interfaces.
There is no claim of literal transcription from a source. Producing a
homogeneous invariant polynomial from this family, proving an invariant
unit-ideal certificate and proving affineness are subsequent obligations.
