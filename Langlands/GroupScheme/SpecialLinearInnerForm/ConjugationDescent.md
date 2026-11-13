# Descending matrix conjugation

This internal algebraic support module is derived from the spanning argument in
`MatrixSpan`. It supplies the coefficient descent step for the matrix action
of a supplied adjoint quotient.

`conjugationAlgHom` bundles conjugation by an invertible matrix as a unital
algebra endomorphism. Its laws follow from associativity, distributivity, the
two inverse equations and centrality of scalars.

`image_of_specialLinear` uses the inverse image of the range submodule and
`span_specialLinear` to extend image containment from determinant-one matrices
to all matrices.

`descendMatrixAlgHom` takes two algebra maps with a common target, the first
injective, and a preimage for the second map on each determinant-one matrix.
It chooses the unique preimage of the second map on each matrix. Applying the
injective first map proves all algebra-homomorphism laws.
`map_descendMatrixAlgHom` records the resulting coefficient-change equation.
No assertion of Galois descent or inner-form classification is made here.
