# Transport of the full character-lattice Weyl image

This internal construction derives from the published actual normalizer and
character-action transport in `Rational.CrossTorusWeylTransport`, the
character identification in `Torus.LatticeGalois`, and Mathlib's conjugation
of general linear groups. It supplies a reduction used in proving
`SplitTorusWeylImageFiniteStatement`.

Over an arbitrary base scheme, let `e : T ≅ T'` be an isomorphism of
commutative group schemes and `f : G ≅ H` an isomorphism of ambient group
schemes, with the actual commuting square
`i ≫ f.hom = groupHom e.hom ≫ j`. Assume that both embeddings are
monomorphisms on their underlying schemes. No torus, splitness, closedness,
maximality, smoothness, reductivity or finiteness assumption is needed for
the transport construction.

The character identification `c = characterLattice.congr e` precomposes
with `e.inv`. `characterAutomorphismTransport e` is the multiplicative
equivalence of integral linear automorphism groups sending an automorphism
`a` to `c ∘ a ∘ c⁻¹`. It is obtained by conjugation on Mathlib's general
linear groups and their standard equivalences with linear automorphisms.
The published `weylAction_transport` shows that this conjugation sends the
action of every source normalizing point to the action of its image under
`normalizerPointsTransportEquiv e f h`.

Consequently `weylImage_map_transport` identifies the conjugated source
image with the target image. The reverse inclusion uses the inverse
normalizer equivalence. Restricting conjugation and then applying this
subgroup equality constructs `weylImageTransportEquiv`. Its injectivity and
surjectivity show that finiteness of either full Weyl image is equivalent
to finiteness of the other. These are images on the entire character
lattices, including all directions outside any root span.

Finally, `splitTorusWeylImageFinite_of_standard` reduces the published full
finiteness statement to its standard split-torus case. Its premise ranges
over every field in an arbitrary universe, every affine group scheme
locally of finite type over that field, every finite index type, and every
closed embedding of the standard split torus. Given a closed split torus
`i : T.toGrp ⟶ G`, choose its splitting `e : T.toGrp ≅ splitTorus _ I`
and apply the premise to `j = e.inv ≫ i`. Composition with an isomorphism
preserves closedness. The induced commutative-group-scheme isomorphism and
the identity of `G` give the required commuting square, so Weyl-image
transport gives the original finiteness conclusion.

The module retains standard split-torus finiteness as a premise. It proves
no preservation or generation result for representation weights and no
unconditional Weyl-image finiteness theorem. It is a supporting unit for
the central-isogeny root-datum proof.
