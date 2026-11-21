# The commutative group law on a Néron model

`NeronModel.ofScheme` takes a scheme over a discrete valuation ring with
the Néron model properties and an isomorphism from an abelian variety to
its actual generic fibre. It returns a `NeronModel` on the supplied scheme
whose generic identification is an isomorphism of commutative group
schemes.

The Néron mapping property gives a bijection on maps from smooth test
schemes upon restriction to the generic fibre. The full category of
schemes with the Néron model properties has finite products. The mapping
property for a product follows by applying the mapping property to both
projections. Restriction to the generic fibre is a fully faithful
Cartesian monoidal functor on this category. The implementation lifts the
group law of the given abelian variety along that functor. Faithfulness
reflects commutativity, and the specified generic isomorphism identifies
the lifted law with the original law of the abelian variety.

## Provenance

This implements the group law extension of Bosch, Lütkebohmert and
Raynaud, *Néron Models* (1990), §1.2, printed p. 14, Proposition 6. The
underlying scheme with the Néron mapping property is an input.
