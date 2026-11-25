# Artinian detection of centrality with arbitrary ambient group schemes

This internal extension of the published
`Langlands.GroupScheme.Reductive.ArtinianCentrality` removes its affine ambient
scheme hypothesis. It uses the arbitrary-target detection theorem proved in
`Langlands.AlgebraicGeometry.Deformation.ArtinianGeneralSchemeDetection`.
The universal product of the source and ambient group must still be locally
noetherian.

For group schemes `H` and `G` over `S`, and a homomorphism `i : H → G`,
`ArtinianCentrality.isCentral_of_artinian_baseChange_general` assumes that `i`
becomes central after every base change `Spec A → S`, where `A` is a local
Artinian ring in the same universe. It concludes `IsCentral i`. No affineness,
separatedness, multiplicative-type, or monomorphism condition is imposed on
these groups or this homomorphism.

The proof adapts the published affine-target argument. It compares the two
multiplication morphisms on `H ×_S G`. For each Artinian probe of this product,
composition to `S` defines a base change. The actual pullback point equivalence
`baseChangePointsEquiv` transports the two tested universal points into the
pulled-back groups. Their commutation follows from the centrality hypothesis.
The general scheme-morphism detector gives equality of the two multiplication
maps. The published `isCentral_of_universal_commute` then supplies centrality
with its full condition after every restriction of test schemes.

When `i` is a monomorphism,
`commGroupSchemeOfArtinianCentralityGeneral` bundles the same group scheme `H`
and its operations as a commutative group scheme, using
`IsCentral.commGroupScheme`. Its `toGrp` equality is reflexive.

This module provides an Artinian detection step for SGA 3, Exposé IX, Théorème
5.6(b). It does not prove centrality over Artinian bases from residue-field
centrality, or remove the locally noetherian universal-product hypothesis.
It does not claim the full arbitrary-base fibrewise-centrality statement.
