# Inversion and continuity of the rank-one upper cell

This module contains the unchanged `rankOneExtensionUpperCell_inv` and
`continuous_rankOneExtensionUpperCell` declarations formerly in
`RankOneExtensionCompactSectionProof`. It imports the actual cell construction
from `RankOneExtensionCellAlgebra` and retains the namespace
`Langlands.RankinSelberg`.

For a field `R`, the cell satisfies `u(y)⁻¹ = u(-y)`. With a topological-ring
structure on `R`, `y ↦ u(y)` is continuous for the existing topology on the
general linear group: its entries are continuous, and the inverse formula
gives continuity of inverse entries. No locally compact or local-field
hypothesis is used.

The compact-section proof and the unfolding-integral construction import
these same declarations. The relocation changes neither statement nor proof.
