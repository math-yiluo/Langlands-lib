# Injectivity and openness for analytified immersions

This internal helper proves the open immersion part of the algebraic-space
analytification immersion theorem. `OpenImmersionEmbeddingStatement` quantifies over
an arbitrary universe `u`, a complete ultrametric nontrivially normed field `K`, a
morphism `f : X′ → X` with separated target, two supplied analytifications and a
compatible analytic map `F`. It asserts that an open immersion `f` induces an open
embedding of underlying analytic spaces. No separate source separatedness or
local finite-type hypothesis is required. It does not assert the closed immersion
conclusion or completion of the full immersion target.

## Implemented proof

`map_injective_of_mono` first proves injectivity whenever the underlying presheaf
map of `f` is a monomorphism. Represent two analytic source points on affine test
charts using joint surjectivity. The finite polynomial surjections give finite-type
coordinate algebras. Separatedness of the target gives their finite-type affine
intersection through `hasFiniteTypeAffinePullbacks_of_separated`.
The target analytification's affine pullback clause and
`exists_point_of_isPullback` lift the two chart points to a point of the analytic
intersection. Its algebraic pullback equation, combined with componentwise
injectivity of the presheaf monomorphism, says the two changed source test points
are equal. Naturality of the source point family makes the two analytic source
images equal.

`isOpenMap_of_isEtale` proves openness for every algebraic étale map. The published
`pointHom_map` from `SpaceAnalytificationEtaleReduction` identifies each pushed
test point with the composite of the source test point and `f`. That composite is
étale, so its analytic map is open by `etaleOpenMap`. For an open source set, its
inverse image on a chart is open by continuity, and its image in the target is
open. Compatibility with `F` puts this image inside the image of the source set.
Joint source-chart surjectivity gives such an open neighborhood of every image
point.

A relative open immersion is étale and a monomorphism because its represented
scheme projections have these properties. General relative monomorphisms are
monomorphisms of presheaves by the published
`SliceOpenGluing.relative_monomorphisms_le_monomorphisms`; the more specialized
`SliceOpenGluing.open_mono` applies only when the source is represented, so it is
not used here. Continuous, injective and open maps are open embeddings. The
module also proves the analogous elementary monomorphism lemma for relative
closed immersions for the later closed embedding argument.

## Provenance

This is an internal consequence of the Library's actual affine-test definition of
`IsAnalytification`, its finite-type represented intersections, its proved ordinary
point lifting for localized analytic pullbacks, and its proved étale open-map
result. The proof uses those constructions, not an assumed fibre-product or
étaleness preservation statement for general algebraic-space analytification.
The formulation retains the actual compatible family of analytic maps and only
concludes a statement about their underlying topological spaces.

The proof uses `pointHom_changeRing` from the étale reduction and `PointOpenSubspace.isEtale_of_isOpenImmersion` for the algebraic open immersion.
