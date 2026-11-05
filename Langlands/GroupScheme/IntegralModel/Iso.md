# Compatible integral-model isomorphisms and original point images

This internal transport construction extends the published `IntegralModel.Hom`
interface. It applies to arbitrary supplied integral models over the same
domain and fraction field, at every universe parameter. It assumes no
smoothness, reductivity, topology, local-field structure or building data.

`IntegralModel.Iso M N f` consists of an isomorphism between the actual
integral group schemes and its compatibility square with the two supplied
generic identifications and a specified generic-group isomorphism `f`.
The compatibility square is part of the data: an abstract isomorphism of
the integral schemes alone is not asserted to preserve their point images
in the specified generic groups.

`Iso.toHom` retains this square in the existing model-homomorphism interface.
`Iso.integralSectionsEquiv` composes actual integral sections with the model
isomorphism; composition with its inverse proves that this is a multiplicative
equivalence. `Iso.integralPointMap_naturality` is the existing naturality
theorem specialized to this compatible map.

`Iso.map_integralPoints` proves equality of the image of the original
`M.integralPoints` under the specified generic map with `N.integralPoints`.
One inclusion uses model-map naturality. For the other, an actual integral
section of `N` has a preimage under the section equivalence, and naturality
identifies its generic image. For an isomorphism compatible with the identity
of one fixed generic group, `Iso.integralPoints_eq` specializes this to literal
equality of the original subgroups in that group.

The provenance is internal: the constructions use only the published
`IntegralModel` definitions, their supplied generic identifications, existing
model-map naturality, and the category and group laws. They provide transport
for a future comparison with a canonical model, but construct no such model
isomorphism. They do not prove a building comparison or maximal compactness.
