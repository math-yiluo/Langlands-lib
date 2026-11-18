# Finite Galois field points on an étale source

Over a complete nontrivially normed ultrametric field `K`, fix a point on the
source of an étale analytic map whose image is the projection of a full
`K`-valued point on the target. The source point is the projection of a full
point with values in a finite Galois extension of `K` in the same universe.
The extension uses its complete ultrametric spectral norm.

For an all-pieces étale strong map between constructed saturations, choose
recognized charts at the given point with finite Banach pullback and
pointwise étaleness. The full base-field point supplies a character into
`K` on the recognized target. Injectivity of the chart embedding shows
that its seminorm is the restriction of the selected source seminorm.
The completed residue at the source is finite over `K` by finiteness of
the bounded pullback and separable by its pointwise unramifiedness.

Take the normal closure of this finite separable field in the separable
closure of `K`. The completed residue embeds isometrically into it.
Postcomposing the canonical residue map gives a character whose norm
realizes the given source seminorm. The domain completed-residue comparison
extends this character to a full point of the recognized atlas. Transport
along the local-domain quasi-isomorphism gives a point of the constructed
saturation with the specified underlying point.

For a localized étale morphism, transport the source point and target full
point back through the arrow isomorphism in the definition of étaleness.
The arrow square and projection naturality identify their underlying images.
Apply the strong result and transport the resulting full point forward. The
inverse identities on the source and projection naturality give the required
underlying point.

## Provenance

The construction is an internal deduction from the Library's pointed finite
étale chart selection, completed-residue results for finite unramified maps,
full chart character extension, and localization. Mathlib supplies the
normal closure and spectral norm, and `AlgebraicEmbedding` gives the
isometry for the embedding of the completed residue.
