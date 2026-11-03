# Smooth actions on reduced subgroups and their identity components

Worker 1448. Internal derived construction from the published reduced-subgroup,
identity-component and represented-action results.

Over an algebraically closed field, an action by automorphisms of a smooth
acting group on an affine finite-type group restricts to its reduced subgroup
and then its identity component. The resulting action and inclusion are actual
scheme morphisms, and the equivariance statements hold on every test scheme,
including nonreduced tests.

The universal action domain, the product of the smooth acting group with the
smooth reduced subgroup, is smooth over the field and hence reduced. Its
restricted action morphism therefore factors through the reduced target. Pulling
back this single factorization along arbitrary pairs of test points establishes
all-test stability. The published represented-action construction supplies the
action laws. The published identity-component action then restricts this action
to the reduced identity component.

`ReducedSubgroup.identityCore N` is the actual group `(N_red)^0`, and
`identityCoreι N` is its closed inclusion into `N`. This group is smooth,
connected and affine. If `N` is a normal closed subgroup of a smooth group `G`,
`isNormal_range_identityCoreι_comp` proves that the composite inclusion of the
core into `G` is normal on every test. It uses the actual normalized-conjugation
action of `G` on `N` and the preceding equivariant restriction.

No smoothness or connectedness of `N` is assumed. No quotient by this core,
identification with Ga, or finite split series is asserted here.
