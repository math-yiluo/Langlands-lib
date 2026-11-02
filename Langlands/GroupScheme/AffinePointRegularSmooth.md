# Regular-smooth families of actual affine group points

Author: Worker 1203. The imported regular-evaluation interface was authored by
Worker 274.

Let `k` be an `RCLike` field in `Type`, and let `G` be an actual affine group
scheme over `k`. Both `k = ℝ` and `k = ℂ` are included. The parameter space is a
charted space with an explicit real model with corners `I`; this comparison
needs no source manifold assumption.

`regularSmooth_iff_coordinateSmooth` identifies the regular-function test on
`RingPoint k G.X k` with `G.CoordinateSmooth` for the coefficient algebra `k`
and the identity coefficient homomorphism. The family is transported by
`affinePointsRingPointHomeomorph`, whose underlying map is the identity on
actual relative scheme morphisms. The equality of evaluations proves the
equivalence for every regular function.

`coordinateSmoothRegularSmoothFamilyEquiv` constructs the resulting equivalence
between the two subtypes of families. Its inverse uses the inverse of the same
homeomorphism. The application lemmas specify the point maps explicitly.
`CoordinateSmooth.continuous` proves that the identity-coefficient criterion
implies continuity for the existing group-point evaluation topology.

`regularSmooth_inv` and `regularSmooth_mul` transfer preservation of the
criterion from the existing coordinate-smooth preservation results. They use
the original categorical point group, exposed locally by `ringPointGroup`.
They introduce no global group instance, replacement law, or topology.

This is internal derived infrastructure. It combines the existing actual
carrier homeomorphism, equality of evaluations, and the two regular-function
family predicates. It constructs no manifold and proves no implication from
algebraic smoothness to an analytic chart. Comparison with smoothness into the
manifold constructed from algebraic smoothness remains a separate obligation
of task `ab4a68f8-804a-4381-88f6-4f97d57779a7`.
