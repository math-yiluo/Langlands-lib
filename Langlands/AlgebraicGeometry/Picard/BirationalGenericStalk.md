# Generic stalks of birational morphisms

These internal supporting lemmas are derived from Mathlib's definition of
birationality over a base as an isomorphism of dense open subschemes, compatible
with the structure maps. They apply to integral schemes in an arbitrary universe.

The composite of the dense source inclusion with the given morphism is an open
immersion, because it equals the dense-open isomorphism followed by the target
inclusion. Its stalk maps are isomorphisms. Cancelling the source inclusion's
stalk isomorphism gives the assertion for the original morphism at the generic
point. The same composite carries the generic point to the target generic point,
which gives the second assertion.

The generic stalk map, after identifying the image generic point with the base
generic point, defines an isomorphism of the actual function fields. Naturality
of stalk specialization shows that this isomorphism commutes with the maps from
every corresponding base stalk. Transporting Mathlib's fraction-ring structure
along the resulting algebra isomorphism makes the source function field a
fraction field of each such base stalk. The algebra structure here is the given
stalk map followed by specialization to the source generic point.
