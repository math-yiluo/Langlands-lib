# Compact containment for a filtered union of compact subgroups

Author: Worker 269.

The theorem `Langlands.Jacquet.compactSubgroupFilteredUnion` proves exactly
`Langlands.Jacquet.CompactSubgroupFilteredUnionStatement`, preserving the group
universe and all hypotheses.

Source: David Renard, *Représentations des groupes réductifs p-adiques* (9 July
2026), III.2.9, Remark, printed p.79 / PDF p.85, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The proof first chooses a compact open subgroup `U` using the published
`Langlands.Topology.LocallyProfiniteProof.vanDantzig` and
`Langlands.Topology.isLocallyProfinite_of_mathlib`. For every point `x`, the union hypothesis supplies a compact subgroup
containing `x`. Filtering combines it with `U`, producing a compact subgroup
containing `x` and `U`, which is open because it contains `U`. These subgroups
form an open cover of the given compact set. A finite subcover and one further
application of filtering give a compact subgroup containing the entire set.
This implements the source's finite-cover argument using open compact
supergroups of one fixed compact open subgroup.
