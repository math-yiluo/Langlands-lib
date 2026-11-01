# Identity and composition of exact functors

These are the existing `Langlands.Derivative.LevelCalculus.mapsShortExact_id` and
`mapsShortExact_comp` lemmas, extracted unchanged from `LevelCalculus` during
integration. The namespace and public statements are preserved.

The identity functor on smooth complex representations preserves short exact
sequences of underlying intertwiners. A composite of two functors with this property
also has it: apply the first exactness hypothesis, then the second to the resulting
maps. Group universes are independent, with one common representation-carrier
universe. The predicate is the published `Mirabolic.MapsShortExactIntertwiners`.

Only `MirabolicMinusExactnessStatement` is imported. The two elementary laws assume
no minus-exactness theorem, derivative detection, homogeneity, or classification
result. This extraction lets the general-linear derivative exactness proof reuse
them without depending on the downstream `LevelCalculus` module.
