# The Schur function at `(0, …, 0, -1, …, -1)`

Module `Langlands.Representation.Shahidi.OpenCellBaseSchur`, namespace
`Langlands.Shahidi.OpenCell.Base`.

`satakeSchur_baseKappa`: for `D ≤ t + 1`, the Library's Schur function at the weight
`κ(t, D) = (0, …, 0, -1, …, -1)` (`D` entries `-1`) is the elementary symmetric function of the
inverse parameters, `s_κ(c) = e_D(c⁻¹)`. The proof passes to the dual weight
(`dualWeight_baseKappa`, `Conductor.satakeSchur_inv`) `(1, …, 1, 0, …, 0)` and evaluates the
Jacobi–Trudi determinant (`jacobiTrudi_initialIndicator`).

## Provenance

Standard identity `s_(1^D) = e_D` for Schur polynomials.
