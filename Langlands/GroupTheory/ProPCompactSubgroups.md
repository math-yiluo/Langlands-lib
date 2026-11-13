# Compact subgroups of pro-p groups

This internal topological-group construction uses the Library predicate
`Langlands.Cohomology.IsProPSubgroup`. The source and ambient groups may live in
different universes.

For a homomorphism `f : G →* Q` inducing the topology on `G`, where `Q` is a
compact totally disconnected topological group,
`exists_openNormalRefinement` proves that every open normal subgroup `N` of
`G` contains the inverse image of an open normal subgroup of `Q`.
`openNormalRefinement` chooses such an actual ambient open normal subgroup and
retains this containment. The proof writes the open subset `N` as the inverse
image of an ambient open neighborhood of the identity, then applies Mathlib's
open normal neighborhood theorem for profinite groups.

`IsProPSubgroup.of_isEmbedding` considers subgroups `H ≤ G` and `K ≤ Q`,
where `Q` is a topological group. Suppose `K` is pro-p, `H` is compact in its
original ambient topology, and a homomorphism `f : H →* K` is a topological
embedding. Then `H` is pro-p for its original subspace topology. Total
disconnectedness transfers along the embedding. For every open normal `N` of
`H`, choose an ambient refinement `M` in `K`. Since `K / M` is a p-group, a
p-power of the image of each element is trivial modulo `M`. The refinement
containment makes the same p-power trivial modulo `N`. This proves the
required p-group assertion for every open normal quotient of `H`.

`IsProPSubgroup.of_compact_le` specializes this result to the literal inclusion
of a compact subgroup in a pro-p subgroup of one topological group.
`IsProPSubgroup.of_isClosed_le` applies it to a closed subgroup of the ambient
group contained in a pro-p subgroup: closedness and the containing subgroup's
compactness supply compactness.

The provenance is an internal argument from induced topologies, compactness,
total disconnectedness and the defining p-group quotients. No structural
theorem about algebraic groups is assumed.
