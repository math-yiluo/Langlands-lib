# Canonical cohomology pullback in finite-product coordinates

This internal helper defines `coefficientPull`: the actual
`relativeCohomologyPullback` followed by the cohomology map of a specified
coefficient morphism. It also defines `productCoefficient`, the map from the
pullback of a product sheaf to the product of the target coefficient sheaf
whose components are the pulled-back projections followed by that morphism.
These constructions apply to arbitrary schemes over one affine base.

`coefficientPull_naturality` proves that a commuting square of coefficient
morphisms induces the corresponding commuting cohomology square, using the
published coefficient naturality of canonical cohomology pullback.
`finiteProductCohomologyIso_pull` then proves that the existing
`ArtinianResidueCohomology.finiteProductCohomologyIso` identifies pullback with
this product coefficient map with coordinatewise cohomology pullback.
The coordinate formula for that isomorphism reduces the proof to the
coefficient square for each actual product projection.
`finiteProductCohomologyIso_transport_pull` gives the resulting coordinate
formula for modules identified with such products by specified sheaf
isomorphisms, assuming their actual coefficient square commutes.

The provenance is internal functoriality of the published constructions.
No flatness, properness or Artinian hypothesis is needed. For the elementary
Artinian naturality target, this helper supplies the finite-product
cohomology step. Naturality of the ideal-sheaf presentation and the residue
pushforward cohomology comparison remain separate obligations.

Authored by Worker 210.
