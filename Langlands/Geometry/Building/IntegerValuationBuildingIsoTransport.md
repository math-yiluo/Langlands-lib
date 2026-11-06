# Explicit integer-valued building transport

This internal construction transports supplied `IntegerValuationBuildingData v G`
through an actual ambient isomorphism `f : G ≅ H`, for any field `k : Type u`
and explicit valuation `v : Valuation k (WithZero (Multiplicative ℤ))`.
No local-field, topology, completeness, Henselian, discreteness-surjectivity or
residue-field assumption is introduced. This includes the supplied building-data
interface over the actual maximal-unramified field.

The centralizer keeps its source, torus factorization and restriction-evaluation
bijection; its inclusion is postcomposed with `f.hom`. Both the torus and the
integer valuation stay fixed, so its actual negative centralizer translation
stays fixed. Reindexing actual root-group points by `f.hom` proves full V6 for
every transported root-function family. This constructs the transported datum
`mapIso` and does not assert existence of source building data.

`mapIsoReducedBuildingEquiv` is the existing actual CrossTorus quotient
transport, specialized to the identity torus isomorphism. Its equivariance uses
the original rational-point actions and the actual map induced by `f.hom`.
The full point fixer maps onto the transported full point fixer. Rational
character restriction along `f.hom` and its inverse preserves and reflects the
original `characterValuationKernel v`. Thus `map_oneStabilizer_mapIso` identifies
exactly the image of the original `oneStabilizer`, including its character kernel.

`mapIsoApartmentAffineEquiv` uses the same full valuation-family transport.
The canonical apartment chart commutes with the quotient equivalence, and the
full ordinary affine-root sets correspond by inverse precomposition. The
existing affine image lemmas preserve singleton facets and parallel vanishing
root hyperplanes, so reindexing all translated apartments preserves and reflects
both building vertices and special points through this same quotient equivalence.

The provenance is internal specialization of CrossTorus transport to the
explicit integer-valued interface and composition with the established general
affine geometry lemmas. The V6 argument has the same reindexing proof as the
local-field transport, with the existing explicit integer centralizer translation.
This unit constructs no metric, original integral model, integral-image comparison,
unique fixed point or unconditional building comparison. It adds no literature
assertion and does not equip the maximal-unramified field with a local-field
instance.
