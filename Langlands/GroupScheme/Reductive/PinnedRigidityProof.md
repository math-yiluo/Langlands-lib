# Rigidity of automorphisms of actual pinned reductive groups

`pinnedAutomorphismRigidity` proves exactly the published
`Langlands.GroupScheme.PinnedAutomorphismRigidityStatement` at arbitrary
universe. Thus, over any field, an automorphism of an actual affine group
scheme with a supplied split pinning is the identity if it fixes the torus
inclusion and its actual differential fixes each chosen simple-root vector.
The target and its imported Lean/Markdown pairs are unchanged.

The proof applies the published reduction
`pinnedAutomorphismRigidity_of_splitPinnedOppositeFactorPairs` to the new
unconditional `splitPinnedOppositeFactorPairs`. The paired
`SplitPinnedOppositeFactorPairs.md` explains the construction of actual pairs:
isolate a root in a connected reductive cocharacter centralizer, use its
rank-one additive root cell, and map the resulting pair to the ambient group.
`RankOneRootCellFactorPairs.md` explains the cell equation and the explicit
ordered factors. These arguments retain arbitrary characteristic and all-test
root-subgroup membership.

For completeness, the imported reduction uses the proved
`maximalTorusCentralizer` to discharge torus self-centralization. Its
simple-root step trivializes the pinning's actual Lie weight line and uses
natural vector coordinates on the actual root subgroup. Weight-coordinate
uniqueness forces scalar linearity of the restricted automorphism; its actual
differential then forces identity on the root subgroup. The fixed subgroup of
the automorphism contains the torus and these simple root subgroups. Uniqueness
of actual opposite pairs gives fixed normalizer points, and root-datum
reflection induction propagates fixedness to every root subgroup. Closed
torus-and-root generation makes the fixed subgroup the whole group.

These scalar, differential, and generation steps are imported from the
published `PinnedRigidityReduction`, `PinnedRootFixedness`,
`RootSubgroupAutomorphismRigidity`, and supporting modules, with their existing
provenance. The new final assembly is an internal composition of these results
with the explicit pair construction. It adds no premise to the target.
