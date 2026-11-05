# Unitary diagonalization of Hermitian cocharacter weight projectors

Author: Worker 1655.

This internal construction gives a unitary diagonalizer for a general linear
cocharacter whose Laurent weight projectors are Hermitian in the given
coordinates. The coefficient field is any `RCLike` field in universe `u`.
Hermitianity is an explicit hypothesis; its existence for a representation of
a supplied rational Levi is a separate obligation.

The linear algebra helper
`exists_unitary_conj_eq_diagonal_of_hermitian_orthogonal` takes matrices `E a`
indexed by an arbitrary type, satisfying `E a * E b = E a` when `a = b` and zero
otherwise, a finite subset on which they sum to the identity, and Hermitianity
of each member. It constructs an invertible unitary matrix `P` and an assignment
`e` of a projector index to each coordinate. Conjugation by `P⁻¹` makes each
`E a` the diagonal projector with entry one exactly where `e i = a`.

For the implemented proof, regard each matrix as a linear map on Euclidean
space and take its range. Idempotence fixes that range, and distinct projectors
kill each other's ranges. Symmetry of the linear maps, obtained from
Hermitianity, makes the ranges orthogonal. Completeness makes their supremum
the entire space, hence they form an internal direct sum. Choose a standard
orthonormal basis on each range and collect the underlying algebraic bases.
Finite dimensionality makes the total sigma index finite even though the
original index type need not be finite. The orthogonal-family theorem shows
that the collected basis is orthonormal. Reindex it by the original coordinate
index, and take its transition matrix from the standard orthonormal basis.
That matrix is unitary. Applying the projectors to its columns gives the
simultaneous diagonal identities. Vanishing ranges and an empty coordinate
index are allowed by the construction.

`GeneralLinear.HasHermitianWeightProjectors χ` is the proposition that every
Laurent coefficient matrix `weightProjector χ a` is Hermitian. The theorem
`exists_unitary_innerIso_comp_eq_diagonalCocharacter` applies the helper to the
published projector multiplication and completeness identities. It returns a
unitary invertible matrix `g` and integer coordinate weights such that composing
`χ` with the actual scheme inner automorphism defined by `baseOfMatrix g`
is literally the published diagonal cocharacter.

Here `g = P⁻¹`; unitary membership passes to the inverse in the group of units.
Every assigned coordinate weight lies in the finite Laurent support, since an
absent projector is zero and cannot have a diagonal entry one after
conjugation. Expand the universal Laurent matrix as the finite sum of the
weight projectors times their Laurent monomials. The simultaneous diagonal
identities transform this sum into the Laurent matrix of the diagonal
cocharacter. The published `eq_of_weightMatrix_eq` then identifies the actual
scheme morphisms. This last comparison follows the existing algebraic
cocharacter diagonalization proof while retaining the additional unitary
property of the chosen conjugator.

The provenance is internal linear algebra and composition with published
cocharacter weight identities. The module constructs neither a simultaneous
star-stable realization of a group and specified Levi nor a compact subgroup.
It is an intermediate result for the supplied-Levi Iwasawa proof.
