# Borel intersection with a torus centralizer

Worker 229.

This is an internal derived result assembling published Library theorems. The
entry proposition `Langlands.GroupScheme.TorusCentralizerBorelIntersectionStatement`
says that, over every field and in every universe, for a smooth connected affine
group `G`, a homomorphism `s : S.toGrp ⟶ G` from a torus, a closed representative
`c : C ⟶ G` of its all-test centralizer, and a geometric Borel `b : B ⟶ G`
containing the range of `s`, the actual pullback projection
`subgroupIntersectionFst c b : subgroupIntersection c b ⟶ C` is a geometric Borel.
The homomorphism `s` is not required to be a closed embedding. The helper
`torusCentralizerBorelIntersection` proves this proposition.

The algebraically closed helper
`IsSplitTorus.isBorelSubgroup_centralizerIntersection` chooses the published
centralizing cocharacter of the split torus. Its centralizer is the torus
centralizer, and its range lies in the given Borel. Dynamic smoothness and
connectedness give these properties for `C`. The restricted cocharacter in `B`
has the pullback intersection as its represented centralizer; dynamic
connectedness therefore makes the intersection connected. The published
`centralizerBorelIntersection` and
`IsBorelSubgroup.centralizer_intersection_borel_iff` then identify the actual
first projection as a Borel subgroup of `C`.

The original-field helper
`IsTorus.isGeometricBorelSubgroup_centralizerIntersection` passes to the algebraic
closure. Finite Galois splitting makes the torus split there; torus centralizers
and range containment commute with base change. Apply the algebraically closed
helper, transport the resulting Borel property through the canonical pullback
comparison isomorphism, and use geometric Borel descent along the algebraic
closure. The last step uses the closedness of the intersection projection and
affineness of `C` inherited from its closed embedding in `G`.

The statement is a reusable actual-pullback strengthening of the first clause of
`TorusCentralizerBorelStatement`; the published target and its imports are
unchanged. No new source translation is asserted: the provenance is the named
published cocharacter, splitting, base-change, connectedness and descent results.
