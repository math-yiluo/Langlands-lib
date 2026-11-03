# Automorphic actions on actual identity components

Work over an arbitrary field `k` in universe `u`. Let `G` be a smooth
affine group scheme and let any group scheme `H` act on `G` through an
actual `AutomorphicAction`. This module derives stability of the actual
identity component `G⁰` on every test scheme. No smoothness, affineness or
connectedness is required of `H`.

The morphism `identityComponentActionHom` restricts the action to
`H × G⁰` in its second argument. Each fibre of the projection
`H × G⁰ → H` is connected because `G⁰` is geometrically connected.
The section given by the identity of `G⁰` belongs to every such fibre and
the action maps that section to the identity of `G`. The image of each
connected fibre therefore lies in the connected component of the
identity. This proves `range_identityComponentActionHom_subset`.
This fibre argument adapts the published proof of normality in
`IdentityComponent.range_conjOver_subset` to an arbitrary action by
automorphisms.

The identity-component inclusion is an open immersion. The existing
`FiniteEtaleImage.liftOver` therefore factors the restricted action after
precomposition with any test point. This proves the all-test stability
statement `isStable_range_identityComponentι`.
`onIdentityComponent` applies the existing `onRepresentedSubgroup`
construction to obtain an actual automorphic action on `G⁰`.
`onIdentityComponent_act_comp` proves that its inclusion intertwines the
induced action and the original action.

More generally, suppose that an action on an ambient group scheme `A`
preserves a subgroup functor `F` represented by a monomorphic
homomorphism `i : C → A`, where `C` is smooth and affine.
`onRepresentedIdentityComponent` first restricts the action to `C` and
then to `C⁰`. Its inclusion into `A` intertwines the action.
`isStable_range_identityComponent_comp` proves that the range of
`C⁰ → C → A` is stable on every test scheme. The ambient `A` has no
smoothness or affineness requirement.

These are internal derived constructions using the existing identity
component, geometric connectedness, open-immersion factorization and
represented-action interfaces. For the semigroup realization problem,
they supply the passage from stability of a smooth affine coordinate
subgroup to stability of its connected representative. Identifying that
coordinate subgroup with the generated semigroup subgroup, identifying
its exact action-weight tangent image, maximality, uniqueness and split
unipotence remain separate obligations.
