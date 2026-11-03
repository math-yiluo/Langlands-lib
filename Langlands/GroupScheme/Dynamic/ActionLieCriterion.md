# Positive Lie weights of arbitrary multiplicative-group actions

This internal supporting module works over every field `k : Type u` with an
affine group scheme `G` and an actual automorphic action `a` of the
multiplicative group. `positiveWeightSpan a` is the supremum, over natural
numbers `n`, of the intrinsic action weight spaces for `t ↦ t^(n+1)`.
The definition needs no finite type or smoothness assumption.

The remaining results assume that `G` is locally of finite type and take
`hLie : DynamicLieStatement.{u}` as an explicit premise. They transfer that
published conjugation criterion to the actual action `a`. They do not assume
the existence of a subgroup representative or that `G` is smooth or connected.

The proof uses the actual semidirect group scheme of `a`. Its underlying
scheme is the product of `G` and the multiplicative group, so it is affine
and locally of finite type. Its normal-factor inclusion is a monomorphism
intertwining `a` and conjugation by the acting-factor inclusion.
The all-test identity-limit functor of `a` is the preimage of the ambient
dynamic unipotent functor. The latter is contained in the normal factor:
the projection is invariant and separated, so it kills every point with
identity orbit limit. These are the published `SemidirectDynamic` results.

`positive_weightSpace_le_range` applies `hLie` to an ambient positive weight
vector. The vector belongs to the ambient dynamic unipotent functor, hence
to the normal-factor subgroup functor. `tangentSubmodule_range` identifies
its tangent membership with membership in the actual derivative range.

`map_positiveWeightSpan` then uses the equivariant weight image formula.
Each image is the ambient weight space intersected with the derivative
range, and the preceding containment makes that intersection the entire
weight space. Linear images preserve suprema, so the whole positive span
maps onto the ambient positive adjoint span. This proves the needed
statement for sums without asserting that inverse images preserve arbitrary
suprema.

`mem_unipotent_iff_iSup_actionWeightSpace` applies the all-test preimage
identity and `hLie`, then reflects membership in the mapped positive span
using injectivity of the actual derivative. It gives the exact dual-number
criterion for the identity-limit functor of `a`. The theorems
`tangentSubmodule_unipotent` and `hasLieImage_unipotent` package the same
criterion as equality of submodules and as the published exact Lie image
predicate.

The provenance is internal, from the published semidirect dynamic
comparisons, equivariant weight functoriality and exact tangent images,
with the conjugation Lie theorem retained as an explicit input. This module
asserts no cyclic-tail comparison or new geometric representability result.
