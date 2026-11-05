# Rational representatives of actual scheme components

Author: Worker 1558.

`IdentityComponent.algebraicallyClosedComponentComparison` proves exactly the
published proposition
`IdentityComponent.AlgebraicallyClosedComponentComparisonStatement.{u}`.
The field and schemes share an arbitrary universe `u`, and the field may have
any characteristic.

For the first conjunct,
`pointComponent_surjective_of_isAlgClosed` assumes only that the actual group
scheme's structure morphism is locally of finite type over an algebraically
closed field. Mathlib's `LocallyOfFiniteType.jacobsonSpace` makes its underlying
space Jacobson. Choose a scheme point representing the desired connected
component using `ConnectedComponents.surjective_coe`. Its connected component is
nonempty and closed, so `nonempty_inter_closedPoints` supplies a closed point
in that component. `pointOfClosedPoint` constructs a morphism from `Spec k`
through this closed point, and `pointOfClosedPoint_comp` makes it a section in
`Over (Spec k)`. The evaluation formula `pointOfClosedPoint_apply` and
`ConnectedComponents.coe_eq_coe'` show that the section has the desired
`pointComponent`. This argument uses no smoothness, affineness, reducedness,
connectedness or global finite type.

For the second conjunct,
`rationalComponentEmbedding_bijective_of_isAlgClosed` retains the published
smooth affine hypotheses. Smoothness supplies local finite type, so the first
helper gives a rational section representing any scheme component. Apply
`rationalComponentProjection` to that section and compute its component with
`rationalComponentEmbedding_projection`. This proves surjectivity of the
existing embedding; its stored injectivity proves bijectivity. The final theorem
packages these two helpers into the exact named proposition.

This is an internal derived proof using the published
`IdentityComponentRationalQuotient` constructions and pinned Mathlib's
`AlgebraicGeometry/AlgClosed/Basic.lean`,
`AlgebraicGeometry/Morphisms/FiniteType.lean`,
`Topology/JacobsonSpace.lean` and `Topology/Connected/Clopen.lean`.
It uses the ordinary quotient of rational sections by sections through the
actual identity component and the actual underlying scheme's connected
components. It constructs no component-group scheme, group law on all
components, sheaf quotient comparison or descent of fixed geometric
components.
