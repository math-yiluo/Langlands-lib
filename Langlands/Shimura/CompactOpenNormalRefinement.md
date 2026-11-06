# Compact open refinements normal in a prescribed level

This is an internal construction from the published `CompactOpenLevel`
definition and Mathlib's
`IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one`.
It introduces no external literature assertion.

Let \(G\) be a topological group and \(U,V\) compact open subgroups.
`CompactOpenLevel.NormalRefinement U V` records an actual compact open
subgroup \(W\) contained in both \(U\) and \(V\), together with normality
of \(W\) as a subgroup of \(U\). The construction is universe polymorphic.
No separation or total disconnectedness hypothesis is imposed.

`CompactOpenLevel.normalRefinement U V` constructs this data. Give the
subgroup \(U\) its induced topology; compactness of the level makes it a
compact topological group. The preimage of \(V\) in \(U\) is an open
subgroup, hence is closed as well and contains the identity. The cited
Mathlib theorem gives an open normal subgroup \(H\) of \(U\) contained in
this preimage.

Map \(H\) into \(G\) along the subgroup inclusion. Its image \(W\) is open
because \(U\) is open in \(G\). As an open subgroup it is closed in \(G\);
its containment in the compact set \(U\) proves compactness. Its
containment in \(V\) follows from the choice of \(H\). For normality, the
implemented proof lifts an element of \(W\) to \(H\) and conjugates that
lift by the given element of \(U\), using normality of \(H\).

For any recorded refinement and an inclusion \(V\leq U\),
`NormalRefinement.normal_fine` proves normality in \(V\) by restricting
the same conjugation law along \(V\leq U\). Thus the construction supplies
a compact open subgroup normal in both levels of any inclusion. It
constructs actual subgroup data only; it makes no assertion about
Shimura scheme existence or geometric transition maps.
