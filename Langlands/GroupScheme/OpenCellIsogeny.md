# Isogenies from finite and surjective maps on open cells

This supporting module, derived from existing Library results, provides a
geometric criterion for an actual group
homomorphism over an arbitrary field to be finite, flat and surjective. The source
is smooth and affine; the target is smooth, connected and affine. Both supplied
cell maps are open immersions, the source cell contains the unit section, and the
commuting map from the source cell to the target cell is finite and surjective.

`HasFiniteSurjectiveOpenCells` packages precisely these chart hypotheses as a
Prop-valued predicate on the actual homomorphism. Its `isIsogeny` theorem applies
`isIsogeny_of_cell`, which also exposes the individual chart data directly.
Surjectivity throughout means surjectivity on underlying scheme points.

First, a locally quasi-finite restriction to an open neighbourhood of the unit
forces finiteness of the full scheme-theoretic kernel. Over an algebraically
closed field, the restriction gives quasi-finiteness at the ambient identity.
The identity fibre is homeomorphic to the full kernel, so the kernel identity is
an open singleton. The published finiteness criterion for affine groups of finite
type with an open singleton then includes the entire possibly nonreduced kernel.
`kernel_isFinite_of_open_chart_algClosed` needs only an affine source locally
of finite type and a separated target; it does not need either group to be smooth.
For an arbitrary field, `kernel_isFinite_of_open_chart` pulls back the chart and its unit section to an algebraic
closure. The actual kernel comparison identifies the pulled-back kernel with the
kernel after base change, and fpqc descent gives finiteness over the original field.

The target cell is a nonempty open subset of an irreducible target group and
is therefore dense. Surjectivity of the cell map and the commuting equation give
dominance of the ambient homomorphism. The published theorem on dominant group
homomorphisms onto reduced groups gives flatness, and the published flat-group
criterion gives surjectivity. The cell restriction is locally quasi-finite,
so the full-kernel criterion applies. Finally, the published fpqc finite-kernel
criterion makes the ambient homomorphism finite.

The provenance is derived from the published smooth connected affine geometry,
dominant-homomorphism flatness, full-kernel and fpqc descent results, and Mathlib's
local quasi-finiteness and fibre-topology APIs. No centrality or smoothness of
the kernel is assumed. This criterion alone does not construct rank-one cells
or prove the general split reductive isogeny theorem.
