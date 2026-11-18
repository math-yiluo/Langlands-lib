# The actual odd dual-number identity kernel in matrix coordinates

Every actual affine dual-number point reducing to the identity has a
unique matrix `1+εY`. The exact affine quadratic and determinant equations
show that its coefficient `Y` lies in the alternating-defect/trace-zero
submodule `lieMatrices`.

Conversely, `TangentPoints` constructs a normalized actual point for every
matrix in that submodule. Matrix addition corresponds to multiplication of
these points because epsilon is square zero. The construction is injective
by coefficient extraction and surjective by the normal form of a matrix
in the identity kernel.

The resulting `tangentKernelEquiv` identifies the actual Library
`lieKernel (groupScheme l K) K` as a group with the additive group of the
explicit matrix submodule (written using `Multiplicative`). No smoothness
assumption on the group is used. This is a group equivalence; scalar-action
compatibility or a linear equivalence is not asserted here.

This internal coordinate argument uses the actual norm-one affine points
and the published general-linear dual-number kernel equivalence. It
introduces no new literature translation. The field has arbitrary universe
`u`, and the finite hyperbolic index lies in `Type`.
