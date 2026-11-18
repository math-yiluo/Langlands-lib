# Homomorphisms of multiplicative-type groups across a thickening

`IsMultiplicativeType.baseChange_hom_bijective_of_surjective_closedImmersion`
proves that base change along a surjective closed immersion of schemes is
bijective on the actual group-scheme homomorphisms between two groups of
multiplicative type over the target. It uses the Library's finite-type,
fppf-local convention for multiplicative type.

`IsDiagonalizable.baseChange_hom_bijective_of_isHomeomorph` transports the
split-model Hom bijection across the isomorphisms witnessing diagonalizability.
`pullHom_bijective_of_diagonalizable` uses this result on a surjective closed
immersion, which induces a homeomorphism on spaces, and uses the pullback
comparisons to express each endpoint as a direct pullback.

`commonEtaleSplittingCover` first chooses an étale splitting neighborhood for
the source at each base point. It then chooses an étale splitting neighborhood
for the pulled-back target at a point above that base point. The composites
cover the base and split both groups by stability of diagonalizability under
base change.

The global proof uses the common cover and its pullback along the closed
immersion. For injectivity, equal reductions give equal restrictions on the
reduced charts. The split Hom bijections give equality on the original charts,
and étale Hom extensionality gives global equality. For surjectivity, the split
Hom bijections lift the given reduced map on every chart. Direct pullback
coherence identifies the reductions of the two restrictions to each overlap.
The split Hom bijection on the overlap gives equality there. Evaluating that
equality on test schemes supplies the compatibility required for étale Hom
descent. The descended map has the required reduction because its reduction and
the given map agree on the pulled-back cover.

This derived module assembles the split topological result, pointwise étale
splitting, and the Library's Hom descent and pullback comparison maps.
