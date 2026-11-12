# A represented relative property tested on an étale atlas

This internal unit generalizes the categorical comparison in the published
`isClosedImmersion_of_etale_atlas`, while retaining representability as an
explicit hypothesis. It does not prove descent of representability.

For a represented transformation `f : F → G`, an étale scheme atlas `h_U → G`
and a scheme test `h_T → G`, `RepresentedAtlas.refinement` is the actual scheme
pullback of the two represented projections over `T`. It maps both to the
represented pullback of `f` along the atlas and to the atlas pulled back over
`T`. The comparison square is cartesian: its outer rectangle is a pullback by
pasting, and the other rectangle is the chosen representation of `f` over `U`.
Cancelling that rectangle gives the asserted square.

`relativeProperty_of_etale_atlas` applies this square to any scheme-morphism
property `P` that is stable under base change and descends along surjective
étale morphisms. If the projection representing the pullback of `f` along the
one surjective étale atlas has `P`, then the projection over every scheme test
has `P`. Indeed, its pullback along the represented surjective étale cover of
`T` has `P` by the comparison square, and scheme descent then gives `P` over
`T`. Together with the supplied representability this is exactly the published
relative morphism predicate.

The constructions use actual schemes in `Over S`, and all test and atlas maps
are full natural transformations. This is a consequence of the imported
relative-representability and pullback machinery, without outside literature.
No limit property or atlas-independence result without the stated scheme
property hypotheses is asserted.
