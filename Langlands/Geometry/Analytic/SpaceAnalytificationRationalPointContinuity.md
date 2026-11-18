# Continuity of the space-analytification rational-point map

Author: Worker 309. This internal unit proves continuity of the existing
`rationalPoint` map for the étale-chart topology. It does not prove
Hausdorffness, injectivity, the inducing property, or the full task target.

Work over a complete ultrametric nontrivially normed field `K : Type u`,
an arbitrary algebraic space `X` over `Spec K`, a localized analytic space
`Y` in the same universe as in the task, and `p : PointFamily K X Y` with
`hp : IsAnalytification K X Y p`. No separatedness or locally finite type
hypothesis on `X` is needed.

`RationalPointMapsContinuous` records continuity for every finite polynomial
presentation `P₀` of `K`. The theorem
`IsAnalytification.continuous_rationalPoint` proves each of these assertions.
The implemented proof passes through the following comparisons.

## Specialization of an affine test point

`IsAnalytification.rationalPoint_changeRing` computes the rational-point map
on a specialization of an affine test point `x : X(A)` along an algebraic
point `φ : AlgPoint K A K`. The result is the analytic point of `φ` in the
affine analytification, followed by the actual chart morphism `p A P x`.

The proof unfolds `rationalPoint`, applies `hp.naturality`, and maps the
composition to underlying continuous maps. The published theorem
`affineAnalytificationRationalPointNaturality` sends the analytic identity
point of `K` along `φ` to the analytic point of `φ`. This gives the required
equality in the actual underlying space of `Y`.

## Affine scheme maps

`IsAnalytification.continuous_affine_schemePointsMap` treats any morphism
from an actual affine scheme `U` locally of finite type over `Spec K` to
`X`. Let `C` be the actual coordinate algebra used by the point-topology
Library. Its finite type instance supplies a finite polynomial presentation.
Use the canonical affine scheme isomorphism to transfer the map `U → X`
to a test point `xC : X(C)`.

For an actual `K`-point `q` of `U`, the coordinate algebra point from
`affineSchemePointEquiv` has spectrum map `q` followed by the canonical
affine isomorphism. Its specialization of `xC` is therefore exactly the
original image of `q` in `X(K)`. The lifted Yoneda evaluation formula proves
this equality. The preceding specialization lemma now expresses the map
as the composition of the affine scheme point homeomorphism, the affine
analytic point map, and the underlying continuous map of `p C P xC`.
The first is a homeomorphism and the second is continuous by the published
`affineAnalytificationRationalPoints` embedding theorem, so the composite
is continuous.

## Scheme and algebraic-space topologies

`IsAnalytification.continuous_schemePointsMap` handles any actual scheme
`U` locally of finite type over `Spec K`. Its existing scheme point topology
is the supremum of topologies coinduced by its affine open point maps.
Continuity from this topology is checked on each affine open. Such an open
is affine and locally of finite type, and its composite with `U → X` is
precisely the affine scheme map treated above. This proves continuity for
the actual scheme point topology.

Finally, the étale-chart topology on `X(K)` is the strongest topology
making all maps from finite-type étale chart schemes continuous.
`etaleChartTopology_continuous_iff` reduces the desired assertion to those
composites. Each chart has a locally finite-type structural map, and its
point map is the evaluation of its underlying presheaf transformation.
The scheme result applies to every chart. This last step does not need a
separate étale openness theorem or a rational-point lifting assumption.

## Provenance

This is an internal deduction from the published `IsAnalytification`
naturality field, the proved affine rational-point naturality and embedding
results, the actual affine scheme coordinate and point homeomorphisms,
lifted Yoneda evaluation, and the published scheme and étale-chart topology
definitions and continuity criteria. It imports the affine proof modules
present in Library commit `97bd11ee61a96b3a3c53624c0db33b8c412bc3f6`.
No new external statement is translated or assumed as an unproved premise.
