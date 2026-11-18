# The actual norm-one group of the split odd form

This internal module defines the group as the actual reduced-norm-one kernel
inside the isometry group of `OddOrthogonalMatrix.form`. Its underlying
relative scheme is affine and locally of finite type. No connectedness,
smoothness or reductivity conclusion is asserted here.

The coordinate vectors in each pair of hyperbolic coordinates form a
hyperbolic family. The existing norm-one family torus therefore constructs
a closed split torus in the actual group. The left-coordinate embedding has
a totally singular image of dimension `Fintype.card l`, giving that lower
bound for the Witt index.

For the reverse bound the module proves the two halves of an arbitrary
hyperbolic family are jointly linearly independent: pairing a linear relation
with each right vector extracts the left coefficients, and pairing with
each left vector extracts the right coefficients. A family therefore uses
twice its length in the ambient dimension. The maximal-family construction
for radical-free forms gives this bound for twice their Witt index.
Applied to dimension `2 * Fintype.card l + 1`, it gives the exact Witt index.
The previously proved radical-free norm-one rank comparison then gives
split rank exactly `Fintype.card l` for the constructed group.

All arguments retain every ground field and characteristic, and the
ambient indices lie in `Type` while the ground field has arbitrary universe
`u`. This is an internal construction from the split odd form and the
published hyperbolic-family and norm-one group interfaces, without a new
literature translation. The type-B root datum, reductivity, form descent and
the central isogeny from an arbitrary type-B group remain separate obligations.
