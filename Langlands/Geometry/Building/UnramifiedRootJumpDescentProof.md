# Proof of unramified descent of vanishing root directions

The theorem `Langlands.Geometry.Building.unramifiedRootJumpDescent` has exactly
the published type `UnramifiedRootJumpDescentStatement.{u}`. It retains the
arbitrary universe, both characteristics and every original binder and
hypothesis.

The proof applies the published theorem
`unramifiedRootJumpDescent_of_rootSpecialization` from
[UnramifiedRootSpecializationStatement](UnramifiedRootSpecializationStatement.md)
to `unramifiedRootSpecialization` from
[UnramifiedRootSpecializationProof](UnramifiedRootSpecializationProof.md).
The first theorem proves
`UnramifiedRootSpecializationStatement.{u} → UnramifiedRootJumpDescentStatement.{u}`;
the second proves its antecedent at the same universe. This application is the
entire implemented proof.

For each fixed upper apartment point and relevant vanishing upper affine root,
the specialization theorem supplies an actual lower root and compatible
integral root specialization data in a common downstairs model. It also supplies
a nonzero scalar relating the lower root form to the restricted upper
derivative. The reduction uses the actual smooth root quotient, its smooth
closed split-unipotent kernel and Henselian lifting to obtain a rational lower
root-group point of value zero. It then applies `LinearMap.ker_smul` to the
nonzero scalar identity to obtain the equality of derivative kernels.

Thus the theorem supplies the rational point and direction required by the
original statement, with no additional premise. The proof uses none of the
final special-point or building-descent statements, or results consuming them.
The published target pair and its dependencies are unchanged.

This is an internal deduction from the two named Library theorems. Its
provenance is their implemented specialization and lifting route; this module
introduces no additional source translation or geometric construction.
