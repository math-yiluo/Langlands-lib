# General nonsingular Hermitian matrix groups

This is internal, derived infrastructure for actual Hermitian matrix presentations.
It generalizes the elementary matrix equations in `HermitianRootMatrices` and
`HermitianRootOpposites` to any finite index type, without changing those modules.
It makes no classification assertion.

`HermitianMatrix.Form c ι` stores an invertible matrix `gram` and the equation
`(gram.map c.bar).transpose = gram`. The coefficient ring is any commutative ring,
including rings of characteristic two. The coefficient involution is the existing
`SU3Root.RingInvolution`, so no global star instance is selected.

The unitary subgroup consists of actual general-linear matrices satisfying
`adjoint c g * gram * g = gram`. Its special unitary subgroup also imposes
`Matrix.GeneralLinearGroup.det g = 1` in the coefficient unit group. Closure follows
by reversing products under adjoint and multiplying by actual inverse matrices.

`Form.map` extends the invertible Gram matrix along an involution-compatible ring
map. `coefficientMap` acts on actual special unitary subgroups whenever the map
carries the source Gram matrix to the target Gram matrix. Its underlying matrix
is entrywise coefficient change. Identity and composition laws are proved for
forms and subgroup elements. These are elementary ring and matrix constructions;
no classification, Witt decomposition or representability theorem is assumed.
