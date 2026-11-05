# Central vector subgroups over a separable closure

This internal construction transports an actual central closed vector subgroup
from any separable algebraic extension of a field to a separable closure of
that field. Its provenance is the existing natural vector coordinates,
base-change transport of centrality and closedness, and the actual comparison
between direct and iterated scalar extension.

`StandardCentralVectorSubgroup G n` records a central closed homomorphism
from the standard dimension-`n` vector group over the same ground field.
`standardCentralVectorSubgroup` normalizes a subgroup's supplied natural
coordinates, and `StandardCentralVectorSubgroup.compIso` transports its
ambient group through an actual isomorphism.

`SeparableClosureVectorSubgroup G n` specializes this structure to a homomorphism from the standard
dimension-`n` vector group over `SeparableClosure k` to the actual scalar
extension of `G`, together with closedness and centrality.
`separableClosureVectorSubgroup` constructs these data from a central closed
subgroup over any separable algebraic extension `K/k` equipped with natural
dimension-`n` vector coordinates. There is no geometric assumption on `G`,
restriction on the characteristic, or finite-degree assumption.

The construction embeds `K` into `SeparableClosure k` using `IsSepClosed.lift`.
It pulls back the original subgroup homomorphism along this embedding,
precomposes with the isomorphism supplied by the pulled-back vector
coordinates, and postcomposes with the inverse of
`baseChangeFieldTowerIso`. Closedness and centrality are transported through
these actual maps and isomorphisms. This is a transport construction; it
asserts neither the existence nor the absence of such subgroups for an
arbitrary group.
