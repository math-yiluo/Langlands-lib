# Identity, composition and surjectivity of exact functors

These are the existing `Langlands.Derivative.LevelCalculus.mapsShortExact_id`,
`mapsShortExact_comp` and `map_surjective_of_exact` lemmas, extracted from
`LevelCalculus` during integration. Their namespaces and public statements
are preserved.

The identity functor on smooth complex representations preserves short exact
sequences of underlying intertwiners. A composite of two functors with this
property also has it: apply the first exactness hypothesis, then the second
to the resulting maps. An exact functor preserves a surjective intertwiner
by applying its hypothesis to the actual inclusion of that map's kernel and
the map itself. The direct kernel-sequence proof is shared with the accepted
Worker 19 filtration contributions. Group universes are independent, with
one common representation-carrier universe. The predicate is the published
`Mirabolic.MapsShortExactIntertwiners`.

Only `MirabolicMinusExactnessStatement` and `Category.Subquotients` are
imported. These elementary laws assume no minus-exactness theorem,
derivative detection, homogeneity, or classification result. Their placement
allows generic exact-functor consumers to reuse them without importing the
downstream `LevelCalculus` module.
