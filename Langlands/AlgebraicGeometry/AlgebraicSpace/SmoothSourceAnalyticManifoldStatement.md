# The analytic manifold structure on rational points of all smooth spaces

This statement formalizes the analytic-manifold assertion of Brian Conrad,
*Weil and Grothendieck approaches to adelic points*, December 31, 2011,
printed p.15, Proposition 5.4, with its proof sketched in the final paragraph
on printed p.16. The registered original is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
For a complete field `k` and a smooth space `X`, Conrad asserts a unique
`k`-analytic manifold structure on `X(k)` that is functorial in `X`, carries
étale maps to local analytic isomorphisms and agrees with the known scheme
case. He does not require a uniform dimension. This module contains no proof; the
statement is proved as `smoothSourceAnalyticManifold` in
`SmoothSourceAnalyticManifoldProof`.

`SmoothSourceAnalyticManifoldStatement` is a proposition definition in
`Langlands.AlgebraicGeometry.AlgebraicSpace`. For every universe-`u` type `K`
with `[NontriviallyNormedField K]` and `[CompleteSpace K]`, it asserts two
things:

1. there is `Φ : DimensionAnalyticStructure K` with `Φ.IsAdmissible`;
2. any two `Φ Ψ : DimensionAnalyticStructure K` with `Φ.IsAdmissible` and
   `Ψ.IsAdmissible` satisfy `Φ.Equivalent Ψ`.

A `DimensionAnalyticStructure K` gives a varying-dimension atlas on the
original rational points `RingPoints K X K` of every smooth, quasi-separated,
locally separated algebraic space `X` over `Spec K`. The topology is the
étale-chart topology. Each point carries a chart of its intrinsic dimension,
and there is no global dimension or finiteness of the set of dimensions.
`IsAdmissible` requires all of the following:

- analytic transitions in every atlas;
- analyticity of the point map of every morphism, in every source and target
  chart pair;
- for étale morphisms, preservation of intrinsic dimension and local branches
  that are analytic with analytic inverses;
- on polynomial affine `n`-space, analyticity in both directions of the
  actual coordinate bijection onto `Kⁿ`.

`Equivalent` means that on every space the actual identity is analytic in both
directions between the two atlases.

The class of spaces is the corrected Proposition 5.4 class: smooth,
quasi-separated and locally separated. Agreement with the scheme case is
encoded by the affine-space normalization. The published pure-dimensional
`AnalyticPointManifoldStatement` uses the same encoding. Together with
functoriality and étale local isomorphisms, that normalization determines the
structure. The statement covers archimedean and nonarchimedean complete fields
alike, as the source does.

This statement differs from the published `AnalyticPointManifoldStatement`. That
statement concerns families of pure-dimensional manifold structures, one for
each relative dimension `n`. The present statement concerns a single structure
on every smooth space of the class, with dimension varying between open pieces.
It also asserts uniqueness among all such varying-dimension structures.

The intended route of a proof is as follows. Every complete nontrivially
normed field is henselian, by the published
`PointTopology.completeHenselianValuedField`. The published canonical
pure-dimensional family is admissible over complete fields. Its
`dimensionStructure` is then admissible by the separate assembly,
functoriality, étale and affine-agreement statements, which gives existence.
Uniqueness is the separate statement
`SmoothSourceDimensionAnalyticUniquenessStatement`.
