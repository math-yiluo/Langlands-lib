# Canonical versus inherited topology on represented standard Levi points: proof

Author: Worker 1505.

This module proves
`Langlands.GroupScheme.StandardLeviPointTopologyComparisonStatement` at every
universe `u`. The theorem is
`Langlands.GroupScheme.standardLeviPointTopologyComparisonStatement_proof`, and
its type is exactly that published proposition. The scope is the statement's.
`F` is any field with any topology. `G` and `M` are actual connected reductive
group schemes over `Spec F`. `i` is a maximal split torus, `ν` a generic
cocharacter, `J` a subset of the simple relative roots, and `j : M ⟶ G` a
closed subgroup representing the all-test subgroup `standardLevi i ν J`. The
proof adds no continuity of the field operations, local compactness,
separation, point-topology comparison or existence of a representation.

## The two topologies

The source `rationalPoints M` carries `rationalPointTopology F M.X`, the
canonical evaluation topology on identity-test points. The target
`standardLeviPoints i ν J` carries `standardLeviPointTopology i ν J`. This
topology is induced from `rationalPointTopology F G.X` by the actual subtype
inclusion into `G(F)`. The proof installs exactly these two topologies as local
instances. It never transports a topology across the group equivalence.

## Affineness and the closed immersion

The statement supplies `IsAffineHom` for the structure morphisms of `G` and `M`
through `IsConnectedReductive.isAffineHom`. The proof then derives
`IsAffine G.X.left` and `IsAffine M.X.left` by `isAffine_of_isAffineHom`, as the
statement does. Its proof-local instances agree with the statement's by proof
irrelevance. The hypothesis `IsClosedSubgroup j` unfolds to
`IsClosedImmersion j.hom.hom.left`.

## Identity-test transport

The published theorem
`Langlands.AlgebraicGeometry.PointTopology.isEmbedding_rationalPointMap` (module
`Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup`) says that
postcomposition `p ↦ p ≫ f` is an embedding of identity-test points when `f` is
a closed immersion between affine schemes over an arbitrarily topologized base
ring. Both carriers have `rationalPointTopology`. That published proof rewrites
the map through the homeomorphisms `rationalPointHomeomorph`, which
`rationalPointEquiv_natural` makes compatible with postcomposition. It then
applies `isEmbedding_affineSchemePointMap` to base-valued affine points. That
theorem rests on the surjectivity of the coordinate pullback of a closed
immersion. Here the theorem is applied to `f = j.hom.hom`, with base ring `F`.

## Restriction to the actual image subtype

Write `ι` for the inclusion `standardLeviPoints i ν J → G(F)` and `e` for
`standardLeviRationalPointsEquiv i ν J j hj`. The composite `ι ∘ e` is
definitionally `x ↦ x ≫ j.hom.hom`, as recorded by
`standardLeviRationalPointsEquiv_val`. So it is inducing by the previous
paragraph. The inclusion `ι` is inducing for the inherited topology, by the
definition of `standardLeviPointTopology` as an induced topology. Mathlib's
`IsInducing.of_comp_iff` then shows that `e` itself is inducing. As a group
isomorphism, `e` is injective, so it is an embedding. It is also surjective.
`isHomeomorph_iff_isEmbedding_surjective` concludes that `e` is a homeomorphism.

## Hypotheses used

The proof uses the connected reductivity of `G` and `M` only for affineness, and
uses the closedness of `j`. The representation `hj` enters only through the
equivalence `e`, whose bijectivity the target module already proves. The
maximal-split-torus, generic-cocharacter and simple-root hypotheses are part of
the statement's scope and are not needed for this topological comparison.
Because no separation is assumed on `F`, the proof uses the embedding result,
not the closed-embedding variant.

## Provenance

This is an internal derivation from published Library results. It makes no
separate claim of translating an external source. The structural and
point-topology sources for the statement are those cited in
`StandardLeviPointComparison.md`. The theorem supplies only this topology
comparison. It does not supply existence of a representation, reductivity of a
represented standard Levi, center comparisons, compactness, modular triviality
or any building, parahoric or decomposition result.
