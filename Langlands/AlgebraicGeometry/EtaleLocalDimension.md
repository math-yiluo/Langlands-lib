# Actual local topological dimension under etale morphisms

Author: Worker 156.

`EtaleLocalTopologicalDimensionStatement` states that every etale scheme
morphism `f : X ⟶ Y` preserves `topologicalKrullDimAt` at every point of `X`.
The theorem `etaleLocalTopologicalDimension` proves it for arbitrary scheme
universe `u`, over arbitrary bases. There is no affine, separated,
quasi-compact, surjectivity, field, or noetherianity hypothesis in this
endpoint.

The local dimension here is the published minimum of the topological Krull
dimensions of actual open neighbourhoods. It is not stalk-ring dimension.
The pointwise conclusion does not assert preservation of the dimension of
every irreducible component for arbitrary schemes.

The algebraic upper-bound helper works for a quasi-finite algebra `S` over
`R` in two independent universes. For a prime `q` of `S`, choose a principal
target neighbourhood attaining the local dimension at its contraction.
The inverse image is a principal source neighbourhood containing `q`.
The localized source algebra remains quasi-finite over the original base,
and hence over the localized target algebra, using restriction of scalars.
The published `ringKrullDim_le_of_quasiFinite` bounds its total dimension by
that of the localized target. Local dimension at `q` is bounded by this
source neighbourhood dimension, giving the required upper bound. Combining
it with the published `topologicalKrullDimAt_comap_le_of_flat_of_isOpenMap`
gives equality for a flat, open, quasi-finite spectrum map.

For an etale map between affine schemes, its global-sections algebra map is
flat, finitely presented, and quasi-finite. Finite presentation and going
down give openness of its spectrum map. The spectrum equality above and the
actual canonical spectrum isomorphisms give the affine comparison.
Choosing a target affine neighbourhood and a source affine neighbourhood
inside its inverse image reduces an arbitrary etale morphism to that affine
case; open embeddings preserve the chosen local dimension.

`HasPureDimension.of_etale` applies the pointwise equality and the published
pure-dimension/local-dimension equivalence for schemes locally of finite
type over a field. Thus an etale morphism into a scheme of pure dimension
`d` locally of finite type over any field preserves pure dimension, without
surjectivity. `hasPureDimension_etale_iff` additionally assumes the etale
map is surjective and gives reflection, by lifting each target point.
Neither corollary assumes quasi-compactness or separatedness. Empty schemes
are permitted, and pure dimension has its unchanged componentwise meaning.

This is internal derived content from the existing Library's actual local
dimension, quasi-finite dimension bound, flat-open local comparison and
locally finite-type pure-dimension comparison, together with Mathlib's
localization, etale and affine scheme APIs. The proof introduces no
additional mathematical assertion from external literature. The intended
consumer is the pure-fibre-dimension chart comparison for algebraic spaces;
this module itself proves no fibre-property or limit-descent assertion.
