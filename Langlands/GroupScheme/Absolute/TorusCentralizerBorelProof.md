# Borel subgroups of a torus centralizer

`Langlands.GroupScheme.torusCentralizerBorel` proves the unchanged published
`Langlands.GroupScheme.TorusCentralizerBorelStatement.{u}` for every universe.
It assumes exactly a field `k`, a smooth connected affine group `G`, a closed
torus `s : S.toGrp ⟶ G`, and a closed representative `c : C ⟶ G` of its
all-test centralizer. There are no additional hypotheses.

For the forward assertion, choose the actual pullback `subgroupIntersection c b`
and its first projection to `C`. The geometric Borel property is supplied by
`IsTorus.isGeometricBorelSubgroup_centralizerIntersection`, proved in the paired
`TorusCentralizerBorelIntersection` module. The equality of subgroup functors is
`range_subgroupIntersectionHom`; it holds on every test scheme.

For the converse over an algebraically closed field, finite Galois splitting
makes the torus split. The algebraically closed helper in the intersection
module proves the Borel property of every actual intersection. Supply this
property to `exists_ambient_borel_of_torusCentralizer_intersections`, whose
proof in the paired `TorusCentralizerBorelConverse` module chooses an ambient
Borel containing the torus, conjugates its intersection within the centralizer
to the prescribed Borel, and conjugates the ambient Borel by the same point.
The point centralizes the torus and preserves the range of the centralizer;
transport through the resulting inner isomorphism preserves intersections.
This gives exactly the required torus containment and all-test range equality.

This is a derived proof assembled from the published Library centralizing
cocharacter and cocharacter-centralizer Borel theorem, dynamic smoothness and
connectedness, finite Galois splitting, base-change and geometric Borel descent,
solvable-subgroup Borel containment, and Borel conjugacy. The implementation
route and its two helpers are described in their paired Markdown. The published
target statement and every pair in its import closure are unchanged.
