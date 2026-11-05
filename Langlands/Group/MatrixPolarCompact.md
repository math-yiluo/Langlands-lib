# The compact subgroup of a polar matrix realization

Author: Worker 1571.

This internal auxiliary construction isolates the compact-overgroup part of a
possible matrix proof of archimedean Iwasawa existence. It does not construct a
matrix realization, polar factors, or an Iwasawa decomposition for a reductive
group.

The scalar field `𝕜 : Type u` is any `RCLike` field, the matrix rank `n` is any
natural number, and the original group carrier `A : Type v` has an independent
universe. All topologies are the existing scalar, matrix, matrix-units and
original group topologies.

`eigenvalue_abs_eq_one` proves that every real eigenvalue on a nonzero vector of
an element of a compact matrix subgroup has absolute value one. For that fixed
vector, maximize its image norm on the compact subgroup. Multiplying a
maximizer by the given element multiplies the maximal norm by the absolute
value of the eigenvalue. This bounds the absolute value by one. Apply the same
argument to the inverse element and reciprocal eigenvalue to obtain equality.
The argument uses the ordinary finite-product norm on vectors.

`eq_one_of_posSemidef` applies this result to every vector of the spectral
orthonormal basis of a positive semidefinite matrix. Its real eigenvalues are
nonnegative and have absolute value one, so all equal one. Mathlib's Hermitian
spectral theorem then makes the original matrix, and hence the matrix unit,
equal to the identity. No unitary-containment hypothesis is used.

`unitarySubgroup ρ` is the subgroup of an original group `A` whose matrices under
a homomorphism `ρ` are unitary. It is defined as the inverse image of the range
of Mathlib's actual `Unitary.toUnits`. `mem_unitarySubgroup` identifies this
definition with literal membership of the value matrix in
`Matrix.unitaryGroup (Fin n) 𝕜`.

`compact_overgroup_eq` assumes that `ρ` is continuous and injective and that
every original element factors inside `A` as a unitary element times an element
whose matrix is positive semidefinite. For a compact subgroup containing
`unitarySubgroup ρ`, both factors then lie in that compact subgroup. Its compact
matrix image has trivial positive semidefinite factor by the preceding theorem.
Thus the original element is unitary, proving equality of the two subgroups.

These are internal derived elementary matrix and compact-orbit arguments. The
existing Library proof `Langlands.Group.unitaryMatrixCompactOvergroup` also uses
compact orbit-norm maximization, but assumes containment of the entire ambient
unitary matrix group. Here no such containment is assumed; the replacement
hypothesis is an explicit polar factorization inside the original group.

The construction currently asserts no compactness of `unitarySubgroup ρ`.
For an actual connected reductive group, a topology-preserving faithful closed
matrix realization, polar factors inside that realization, and coverage by the
actual parabolic image remain separate proof obligations. In particular none
of these auxiliary hypotheses can be added to the closing theorem
`Langlands.Global.InfinitePlaceGroupPoints.ParabolicIwasawaStatement`.
