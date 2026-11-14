# Field matrices for adjoint actions on special linear groups

This internal construction concerns an actual adjoint quotient `q : M ⟶ A`
over any field `K`, and a supplied group-scheme isomorphism from `M` to a
special linear group with any finite coordinate index type. There is no
restriction on characteristic or matrix size.

`adjointMatrixEquiv` upgrades the existing matrix-algebra endomorphism of
an adjoint point to an algebra automorphism. The inverse is the matrix action
of the inverse adjoint point; the existing multiplication and identity laws
prove both inverse equations.

`exists_matrix_for_adjoint_point` applies the published innerness theorem
for field-linear automorphisms of full matrix algebras to this equivalence.
It gives a single invertible matrix over `K`. The existing all-test action
comparison and uniqueness of coefficient extension identify the action on
every test scheme with conjugation by the pullback of that matrix.

`matrixBaseIso` identifies the affine coefficient test of `K` with the base
itself. `sectionMap_matrixBase` identifies coefficient pullback along the
terminal map with the actual structure-ring map `scalarMap`.
`exists_matrix_for_adjoint_basePoint` therefore describes the group-scheme
automorphism evaluated at a ground-field adjoint point by one matrix on
every test, including non-affine tests.

The provenance is internal and derived. The proof combines the published
adjoint matrix action, its coefficient-extension comparison, and
`Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv`. It does not use an
inner-form classification, a Tits cocycle statement, or the desired special
linear automorphism classification. It proves a matrix formula for a supplied
adjoint point, without asserting that every automorphism comes from one.
