# Actual affine tangent points of the odd norm-one group

This module constructs ordinary coefficient-matrix coordinates for actual
affine points of the split odd norm-one group. They are injective and
commute with coefficient-algebra homomorphisms, and every point satisfies
the alternating quadratic defect equation and determinant one over its
original coefficient algebra.

Over the actual dual-number ring, the matrix `1+εY` satisfies these two
equations exactly when `Y` lies in the alternating-linear-defect and
trace-zero submodule constructed in `LieMatrices`. The proof expands the
square-zero quadratic defect and uses the published dual-number
determinant formula.

For every such matrix the module constructs an actual affine dual-number
point of the odd norm-one group. Its coefficient matrix is exactly `1+εY`
and it reduces to the identity. This provides actual tangent-point
witnesses without assuming smoothness of the odd group.

The construction is internal transport through the published affine
norm-one tensor coordinates, scalar matrix chart, and square-zero matrix
identities. It introduces no new literature translation or smoothness,
connectedness or reductivity assertion. The finite hyperbolic index is
in `Type`; the ground field has arbitrary universe `u`.
