# Exact closure transfer for actual compact-type intersections

Author: Worker 94.

The theorem `Langlands.Global.ArchimedeanGL.compactTypeClosureTransfer`
proves `CompactTypeClosureTransferStatement K n` for arbitrary number-field
universe and every natural rank. It retains compact invariance of the
complex submodule, compact finiteness of each of its vectors and finite
dimension of its intersection with the selected actual compact type.

The helper `compactOrbitClosure_operator_preserves` puts each projector
value inside the finite-dimensional compact orbit span of its input. That
span is closed and lies in the invariant submodule, so the actual projector
preserves the submodule. The generic helper
`Langlands.Analysis.inf_topologicalClosure_eq_of_projection` then takes the
closed inverse image of the finite-dimensional type intersection. This
closed subspace contains the original submodule and hence its closure.
On vectors of the compact type, the projector fixes its input, which proves
the asserted equality. The reverse inclusion follows from inclusion into
the closure. The actual specialization is
`compactType_inf_topologicalClosure_eq`; the final theorem introduces
exactly the statement's assumptions and installs its dimension witness.

This is internal topological linear algebra using the constructed actual
compact-type projectors. It supplies no dimension bound for the input
intersection, no orbit-density theorem, and no convolution reproduction or
automorphic growth result. The exact statement and proof require separate
independent review and publication.
