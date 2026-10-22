# P-adic full upper unipotent groups

Author: Worker 6.
Shared Hausdorff-certificate extraction: Worker 26.

For every prime `p`, every algebraic `PadicField p`, every supplied
`TopologicalData` and every natural rank, this module provides the actual
upper unipotent subgroup topology and proved topological-group, Hausdorff
and locally compact certificates. Continuity and separation transfer through
the subgroup inclusion. Local compactness uses the proved closedness in
`UpperUnipotent`, the ambient GL certificate from `Padic`, and the explicit
`T.fieldT2` certificate from
[`LocalField.Topology`](../../LocalField/Topology.md). The shared certificate
retains the former private proof using the compatible right uniform structure
of the supplied local field.

`upperUnipotentSum` is the same first-superdiagonal sum homomorphism from
`UpperUnipotent`, with its proved continuity under the supplied field topology.
It has rank `n + 1` and sums the `n` adjacent coordinates. It assumes no
character, representation, conductor, or compact-open basis.

The four canonical abbreviations use the accepted `canonicalTopologicalData`
for every algebraic field. All structures are explicit, locally selected
values rather than new global topology instances.

This is an internal specialization of the companion `UpperUnipotent` and
`Padic` constructions. Their paired Markdown gives the exact source
conventions and proofs; in particular, the sum agrees with
Jacquet--Piatetski-Shapiro--Shalika (1981), Section 1.2, formula (2), printed
page 200, by the additive-character law. The core artifact
`cd1132db-8cab-4cab-bd28-0c6164b44dbe` version 1 is independently accepted and
published at commit `843c574c920aa9926ab56adf662c74b3cd4ed0e1`, effective snapshot
`42106411fcd47bace4b6e12d64b234b7564303775ee7b633bd3341e60208dd4b`.
Final review receipt `7c88f2621a5047a9a85fe9ef375a8ed0` confirms the unchanged
reviewed pairs, their current dependency closure and successful final Lake validation.

The private `fieldT2` implementation moves to the shared
`Langlands.PadicField.TopologicalData.fieldT2` declaration, available through
the retained `Padic` import. Both original imports and this module's path
remain. Every public declaration retains its full type, selected `T.topology`
and underlying map. See the shared module's
[migration map](../../LocalField/Topology.md#module-and-declaration-migration).
