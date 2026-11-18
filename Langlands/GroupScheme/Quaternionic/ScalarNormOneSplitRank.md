# Split rank of the actual norm-one isometry group

This internal construction places the scaling torus of any scalar hyperbolic
family inside the actual reduced-norm-one isometry group. It applies over every
field, in every characteristic. No smoothness assumption on the full isometry
group or invertibility of the polar matrix is imposed.

The factorization uses the published range criterion on all test schemes:
the family scaling has quadratic defect in the alternating subspace, and
its reduced norm is one by `ScalarHyperbolicNorm`. The ambient scaling map
is a monomorphism, so its factor `IsHyperbolicFamily.normOneTorus` is also a
monomorphism. The published theorem on torus monomorphisms makes this a
closed split subtorus. A family indexed by `I` therefore gives split rank
at least `Nat.card I`.

The reverse inequality follows by the closed inclusion into the full isometry
group and its published Witt-index bound. When the quadratic radical is zero,
`RadicalFreeHyperbolicFamily` supplies a family with length the Witt index,
and the two bounds prove exact equality. The ambient index type is a nonempty
finite type in `Type`; the field has arbitrary universe `u`.
The module also supplies affineness and local finite type for the scalar
norm-one isometry group through its closed inclusion in the smooth affine
matrix-algebra unit group.

These are internal consequences of the actual norm-one kernel, the published
family torus, the scalar norm calculation, the radical-free maximal-family
construction, and the torus Witt-index bound. There is no new literature
translation. The construction proves the rank comparison for a given scalar
form; it does not construct a form from a type-B group or its central isogeny.
