# The multiplicative-group action on a dynamic contracting subgroup

This internal module constructs the actual conjugation action of a
cocharacter on any group scheme representing its contracting subgroup.
The inclusion intertwines that action with ambient conjugation on every
scheme test, including nonreduced tests. The construction restricts the
published ambient action using the published stability and represented
subgroup action interfaces.

Over a field, assume the ambient group is affine and locally of finite
type and the representative is affine. Its zero Lie weight space is
trivial. The inclusion maps a zero-weight vector into the ambient zero
adjoint weight space. The published dynamic Lie criterion puts that
image in the dynamic centralizer; representability also puts it in the
contracting subgroup. Uniqueness of limits makes a point in their
intersection the identity. The representing monomorphism is injective
on the actual dual-number identity kernels, so the original vector is
zero. The weights and tangent maps are the actual group-scheme ones.

For a smooth affine ambient group over a field, a closed representative
is affine, smooth by `dynamicSmooth`, and connected by
`DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent`.
`isUnipotent_of_torusActionUnipotence` applies the general
`RelativeRoot.TorusActionUnipotenceStatement` to this multiplicative-group
action and its trivial zero weight space. That general statement remains
an explicit hypothesis.

The results are derived from the published action, weight, dynamic Lie,
limit uniqueness, smoothness and connectedness APIs. No external
assertion is introduced here. This module supplies the specialization
to the dynamic contracting subgroup; it proves neither the general
torus-action unipotence statement nor reflection existence.
