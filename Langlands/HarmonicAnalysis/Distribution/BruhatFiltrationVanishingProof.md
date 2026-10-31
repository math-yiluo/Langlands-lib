# Finite Bruhat-filtration vanishing from actual open restrictions

Authors: Worker 176 and Worker 634.

`Langlands.HarmonicAnalysis.Distribution.bruhatFiltrationVanishing.{u}`
proves exactly the published proposition
[`BruhatFiltrationVanishingStatement`](BruhatFiltrationVanishingStatement.md).
The theorem preserves its arbitrary universe, every natural rank including
zero, every Hausdorff topological field whose actual group `GL_n(K)` is
locally compact and totally disconnected, and every complex algebraic
distribution on that group.

The sole premise says that, for each permutation `w`, support of this same
distribution `D` on the layer at the inversion count of `w` implies zero
actual open restriction to `upperBruhatCellNeighborhood n K w`. The
conclusion is `D = 0`; an initial support hypothesis is derived within the
proof.

## Implemented proof

The namespace `BruhatFiltrationVanishingProof` contains the three coherent
support-removal lemmas adapted from Worker 634's preparation.

`restrictOpen_compl_layer_zero` assumes that `D` belongs to `supportedOn`
of the closed layer `upperBruhatLayerLE n K k`. A test function on the open
complement extends by zero to a function vanishing on the layer. The
support condition therefore annihilates its extension, so the actual
restriction to the complement is zero. This helper does not require local
compactness or total disconnectedness.

`remove_top_layer` additionally assumes zero restriction on the specified
neighborhood of every cell with inversion count exactly `k`. It applies the
published theorem
[`openRestrictionLocality`](OpenRestrictionLocalityProof.md) to the union
of cells with inversion count strictly less than `k`. For a point outside
this smaller union, there are two cases. Inside the layer at `k`, its cell
has count at most `k` and cannot have smaller count, so its count equals
`k`. The cell neighborhood contains the point and has zero restriction by
the additional assumption. Outside the layer, the open complement contains
the point and has zero restriction by the first helper. Locality gives
support on the smaller union.

`vanishing` keeps the original conditional premise on the fixed `D`.
Induction on `k` proves that support on any bounded layer forces `D = 0`.
At `k = 0`, removing the top count leaves the empty union: no natural
inversion count is strictly negative. Every test function vanishes on this
empty set, so the support condition makes the distribution zero. At
`k + 1`, the smaller union is contained in the layer at `k`, because a
natural count strictly less than `k + 1` is at most `k`.
`supportedOn_mono` and the induction hypothesis then give zero. At each
step the assumed equality of a cell's inversion count with the current
layer transports the support hypothesis to the exact antecedent of the
original conditional premise.

Finally, `exists_mem_upperBruhatCell` places every actual invertible matrix
in a cell. The inversion count is the cardinality of a filtered subset of
`Fin n × Fin n`, hence is at most `n * n`. A test function vanishing on
that layer thus vanishes everywhere. Every distribution consequently
belongs to `supportedOn` of this layer, and the induction applies. The
argument uses no positivity of `n`, so it also handles rank zero.

The production theorem `bruhatFiltrationVanishing` introduces exactly the
quantifiers of `BruhatFiltrationVanishingStatement.{u}` and applies
`BruhatFiltrationVanishingProof.vanishing`.

## Provenance and scope

This is an internal deduction from the published actual upper Bruhat
partition, inversion-layer topology and Schwartz–Bruhat subspace maps.
Worker 634 authored `restrictOpen_compl_layer_zero`, `remove_top_layer` and
`vanishing` in the complete shared parent draft revision 8 of task
`f79ca82c-d050-4ffa-821b-c347b60e36e0`,
`BruhatFiltrationVanishingCore.{lean,md}`. Worker 176 ports those three
lemmas together, imports the public target and locality proof, replaces the
private locality call with `openRestrictionLocality`, and supplies the
exact production wrapper. The locality implementation is imported as
published; its separate attribution to Workers 634, 33 and 121 is recorded
in its own paired explanation.

The statement's Markdown explains the finite support-removal pattern's
relation to Shalika's dimension-indexed argument. This proof uses numerical
inversion counts and needs no comparison with dimension. It performs only
finite support removal from the stated conditional restriction premise.
The cellwise Whittaker vanishing argument and global Shalika invariance
remain separate obligations. No equivariance, transpose symmetry, measure,
continuity of the distribution, finite unipotent-orbit decomposition or
interchange of a distribution with an infinite integral enters.
