# P-adic block subgroup topologies

For every prime `p`, every algebraic `PadicField p`, every supplied
`TopologicalData`, and every ordered positive `BlockShape n`, this module
provides explicit topologies and proofs of the topological-group, Hausdorff
and locally compact properties of the actual parabolic, opposite parabolic,
unipotent radical and product Levi. These are the subgroup and finite-product
topologies of the matrix groups, using precisely the supplied field topology.
No additional group or decomposition is assumed.

Group continuity and separation transfer from the ambient GL certificate
through the usual subgroup instances. For the Levi they transfer separately
to each actual block GL, then to the finite product. Local compactness for
the parabolics and radical uses the closedness proved in `Blocks`. Its
Hausdorff field premise is discharged by the explicit `T.fieldT2` certificate
in [`LocalField.Topology`](../../LocalField/Topology.md), available through
the retained `Padic` import. It uses the same compatible right uniform
structure proof as the former private helper. Local compactness of
the Levi uses the finite product of the block GL certificates.

The continuous block diagonal embedding, diagonal projection and decomposition
homeomorphism are specializations of the actual constructed maps in `Blocks`.
The canonical abbreviations apply these constructions to the exact
`canonicalTopologicalData` already supplied by `LocalField.Canonical`; there
is no realization assumption on the algebraic field. The code installs
structures locally and does not choose a global topology or identify distinct
absolute-value normalizations.

This is internal specialization of `Blocks` and `Padic`, with their precise
matrix and topology conventions and source provenance. The paired `Blocks.md`
describes the intrinsic matrix proofs. The paired `Padic.md` identifies the
published local-field construction dependencies. The core `Basic`/`Padic`
pairs were checked for their dependency closure, and they build with Lake.
Compact-open bases require the separately stated intrinsic GL
nonarchimedean prerequisite.

The private `fieldT2` implementation moves to the shared
`Langlands.PadicField.TopologicalData.fieldT2` declaration. The existing four
local-compactness families and all public topologies, maps and canonical
abbreviations retain their full types and selected `T.topology`. Both original
imports and this module's path remain. See the shared module's
[migration map](../../LocalField/Topology.md#module-and-declaration-migration).
