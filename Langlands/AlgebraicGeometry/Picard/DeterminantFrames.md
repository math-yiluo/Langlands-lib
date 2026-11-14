# Determinant lines from actual finite local frames

This derived construction starts with an actual module sheaf `M` on a scheme
`X`, an open cover `T`, a single finite index type `I`, and an actual free-sheaf
frame of `M.over (T i)` on every chart. The scheme, chart indices, and frame
indices have the same universe. Empty opens and the empty finite frame are
allowed.

`basis` is the actual section basis on a smaller open, using the published
`localSectionBasis`. `matrix i j` has as columns the coordinates of frame `j`
in frame `i`. Its identity and composition laws follow from the corresponding
Mathlib basis-change laws. Both frame vectors and their coordinates commute
with restriction, which proves `matrix_restrict`.

`unit i j` is the determinant of that matrix. The reverse change of frame
supplies its inverse. `unit_restrict` follows by applying the determinant to
the restricted matrix. Restricting these units to pairwise overlaps gives
`cocycle`. The matrix composition law and multiplicativity of the determinant
prove its triple-overlap cocycle equation.

`lineBundle` applies the published actual cocycle gluing construction. Its
sections are families of local scalar functions with coordinates related by
these determinant units; its underlying module sheaf is locally free of rank
one by the proved cocycle gluing theorem. This is the determinant transition
construction for the supplied constant-rank frames.

The provenance is internal: every new equation is derived from published
section-basis restriction identities, Mathlib basis-change matrices and
determinants, and the published actual cocycle line-bundle construction.
Independence of the choice of cover and frames, a sheaf exterior-power
comparison, pullback coherence, variable-rank assembly, and ampleness are
additional obligations. This module does not construct the canonical parabolic
polarization or prove the parabolic representability statement.
