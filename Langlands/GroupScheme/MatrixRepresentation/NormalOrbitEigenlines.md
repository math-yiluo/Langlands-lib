# Eigenlines in normal-subgroup orbit coordinates

This internal helper defines `HasUnitScalarAction`: a representation acts
on a base-field vector by some unit scalar after every scheme test. The scalar
may depend on the test point. This predicate includes no nonzero condition
on the vector.

`normal_unitEigenvector_translate` proves that translating a subgroup
unit-scalar line by an ambient group point preserves its unit-scalar action
when the subgroup is normal on every scheme test. The proof applies the
original line criterion to the conjugate `g⁻¹ h g`, and then multiplies its
matrix equation by the matrix of `g`.

`normal_rationalOrbit_column_eigenvector` applies this argument to a rational
orbit vector and uses the existing constant-point scalar-extension identity.
Thus each rational orbit column has unit-scalar action by the subgroup on
every test, including nonreduced tests.

`restrictCoordinates_eq_diagonal_of_column_eigenvectors` computes the actual
induced split-coordinate matrix. If each inclusion column has the specified
unit eigenvalue, the induced matrix is diagonal with those eigenvalues.
The proof multiplies each column equation by the retraction and uses
`C * B = 1` after scalar extension.

These are internal consequences of the actual point-matrix, normality and
split-coordinate interfaces. They do not require a smooth or reduced
subgroup and do not prove the quotient theorem.
