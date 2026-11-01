# Algebraic restriction of isotypic parts

This internal construction compares the sum of images of a simple
representation with its group-algebra isotypic component, and proves that this
part pulls back along an injective intertwiner. Its route uses algebraic
semisimplicity, with no compactness, topology or averaging hypothesis.

For any ring and simple module, the isotypic component equals the sum of all
linear-map ranges from that module. Each map is zero or injective; every
submodule isomorphic to the source is such a range.

For an injective module map, the inverse image of the ambient isotypic
component embeds into that component. Mathlib proves that this component is
semisimple and isotypic of the source type. Both properties pass to the
embedded inverse image. Decomposing it as a sum of simple submodules shows that
each summand has the source type, proving containment in the internal isotypic
component. Functoriality of the isotypic component gives the reverse inclusion.

`isotypicModulePart ρ σ` names the group-algebra component. For an
irreducible source, `isotypicPart_eq_map_modulePart` identifies its restriction
to complex scalars, transported by the identity coordinate equivalence, with
the existing `isotypicPart`. Mathlib's linear equivalence from intertwiners
to group-algebra linear maps preserves their underlying functions and ranges;
reindexing the two sums proves the equality.

`isotypicPart_comap_of_injective` applies the module pullback result to that
same map viewed over the group algebra. Thus the image of the internal part
is exactly the ambient isotypic part intersected with the intertwiner's
range, as recorded by `isotypicPart_map_of_injective`. The source must be
irreducible for these comparisons. The group and all three representation
spaces may live in independent universes; finite dimension, continuity,
compactness and semisimplicity of the ambient representation are not assumed.
This is a reusable algebraic step, with no assertion about differential
growth or the actual generated smooth-function module.

The provenance is a direct application of Mathlib's simple-module,
semisimple-module and isotypic-component results to the existing sum of
intertwiner images.
