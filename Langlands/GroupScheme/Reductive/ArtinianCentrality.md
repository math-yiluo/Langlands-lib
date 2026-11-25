# Detecting subgroup centrality on local Artinian base changes

This internal module applies the proved local Artinian scheme
morphism detector to the two multiplication maps on the universal product
of a subgroup source and its ambient group. It assumes no group structure
theorem beyond the imported definitions and base-change point comparisons.

For any group schemes H and G over S and any homomorphism i : H → G,
`isCentral_of_universal_commute` proves all-test-scheme centrality from
commutation of the two universal points on H ×_S G. Pulling this equality
back along the pair consisting of a restricted H-point and an arbitrary
G-point gives exactly the all-restrictions centre condition.

`isCentral_of_artinian_baseChange` assumes that the underlying scheme of
H ×_S G is locally noetherian, that the underlying scheme of G is affine,
and that i becomes central after every base change Spec A → S for a local
Artinian ring A in the same universe. The two universal multiplication
maps are equal by `ArtinianDetection.hom_ext`. For each Artinian test of
the product, its composite to S defines the base change. The actual
`baseChangePointsEquiv` identifies its two points with points of the
pulled-back groups, so the assumed centrality gives the required equality.
The preceding universal-pair lemma then gives `IsCentral i`.

If i is a monomorphism, `commGroupSchemeOfArtinianCentrality` retains the
same group scheme H and its operations and supplies commutativity via
`IsCentral.commGroupScheme`. Its `toGrp` equality is reflexive.

The hypotheses on the universal product and the ambient affine scheme
are explicit. This module does not prove centrality over Artinian bases
from residue-field centrality, nor any approximation or arbitrary-base
criterion. It does not prove the fibrewise central-isogeny statement.
