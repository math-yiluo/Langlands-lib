# Products constructed from subcomplex coordinate faces

This is an internal construction using the existing definitions in
`AbstractBuilding`. It introduces no external assertion. It constructs
supported simplicial factors and identifies their finite product with a
nonempty subcomplex closed under independent mixing of coordinate faces.
The original vertex universe `u` and factor-index universe `v` are independent.

For a family of facets `B`, `coordinateSupport B i` consists of coordinate
vertices occurring in some member of `B`. `IsCoordinateMixingClosed B` says
that choosing a facet separately for each coordinate and taking the product
of those coordinate projections gives another member of `B`.

Let `B` be a nonempty subcomplex of a supplied finite-product complex `K`.
The vertices of `subcomplexFactor` are the supported vertices. Its faces are
the nonempty sets whose images in the original coordinate vertex set are
contained in the projection of a facet of `B`. They are finite because that
original facet is finite. All supported singletons occur, and taking nonempty
subsets preserves the same bounding projected facet. This defines an actual
simplicial complex, and `subcomplexProduct` is their actual finite product.

If `B` is closed under coordinate mixing, a tuple of supported factor faces
gives a member of `B`: choose bounding facets for each factor, mix their
projections, and use downward closure of the subcomplex. The smaller product
is a facet of `K`, since each coordinate face is a nonempty subface of an
original simplicial face.

`subcomplexFactorCoordinates` sends each original facet to its coordinate
projections, regarded as faces on the supported vertex types. The
`subcomplexCoordinatesOrderIso` has this map as its forward direction. Its
inverse takes the product of the images of the supported factor faces in the
original coordinate vertex types. The mixing argument just proved establishes
that this inverse product is a member of `B`.

The two inverse identities use the literal product structure of the original
facets, and the fact that projecting a nonempty product recovers each factor.
All coordinate values of an original facet lie in the supported vertex types.
Preimage of the image of a supported face recovers that face because the
subtype inclusion is injective. Finally, inclusion of the supported coordinate
faces is equivalent to inclusion of the original product facets.

Composing with the existing facet-to-coordinate order isomorphism for the
constructed finite product gives `subcomplexProductOrderIso`. Thus the
construction identifies the original facets and their inclusion order with
the facets of an actual polysimplicial complex. Transporting that complex's
`IsPolysimplicial` witness gives
`isPolysimplicial_of_coordinateMixingClosed`.

The construction applies to empty index sets as well. Nonemptiness of `B`
is retained explicitly. An arbitrary subcomplex need not be closed under
coordinate mixing; this is an explicit sufficient condition, and is not
claimed to follow from polysimpliciality of an arbitrary subcomplex with some
other factorization. No property of actual valuation building apartments,
nor the unconditional `RootValuationBuildingConstructionStatement`, is
asserted here. An application to an actual apartment must prove the mixing
condition for its chosen ambient coordinates.
