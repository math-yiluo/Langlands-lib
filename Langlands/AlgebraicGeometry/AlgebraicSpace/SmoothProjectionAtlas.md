# Smooth endpoint atlases from a smooth scheme cover

This module is an internal construction for the smooth-relation quotient
interface. It keeps smoothness descent along a smooth surjective source map
as an explicit hypothesis `hDescent`. It does not prove that descent theorem.
All schemes are arbitrary schemes in the universe `u`.

`SmoothProjectionAtlas R s t` records an actual etale surjective scheme atlas
of an algebraic space `R`, actual morphisms from its source scheme to the
object scheme `U`, the two natural-transformation compatibility equations,
and smoothness of both scheme morphisms. Its `hasSmoothProjections` lemma
forgets the chosen data to the published existential
`SmoothRelationQuotient.HasSmoothProjections`.

For `smoothProjectionAtlasOfSmoothCover`, suppose an actual scheme `A`
maps smoothly and surjectively to `R` through a representable transformation
`q`. Suppose both composites of `q` with the endpoints `s` and `t` are the
Yoneda maps of smooth scheme morphisms `sA` and `tA`.

Choose an etale surjective scheme atlas `b : W → R`. Representability of `q`
gives the actual scheme pullback `P = A ×_R W`, with smooth surjective
projection `p : P → W`. Its projection `a : P → A` is etale because it is
the base change of `b`. Full faithfulness of lifted Yoneda identifies the
composites `b ≫ s` and `b ≫ t` with actual scheme morphisms `sW, tW : W → U`.
The pullback square and the given endpoint equations imply
`p ≫ sW = a ≫ sA` and `p ≫ tW = a ≫ tA`.
These composites are smooth by composition of the etale map `a` with the
given smooth endpoints. Applying `hDescent` along the smooth surjective map
`p` proves smoothness of `sW` and `tW`. The construction returns `W`, `b`,
these two endpoints, and all their properties.

The argument requires smooth-surjective source descent: `p` is the base
change of the smooth map `q`, and need not be etale. No finite type,
quasi-compactness, or separation hypothesis is imposed. The source-descent
input and the smooth-surjectivity of `q` are not inferred from any pending
publication. This generic construction is independent of the Picard case.
