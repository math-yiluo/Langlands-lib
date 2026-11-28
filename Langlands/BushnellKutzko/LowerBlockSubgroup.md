# The subgroup with a deeper lower corner

`SplitBlocks.lowerBlockSubgroup` takes a lattice chain, integral block projectors
`e₁`, `e₂` with `e₁ + e₂ = 1`, and a subgroup of `Uᵐ` for `m ≥ 1`.
Its elements `g` satisfy `e₂(g − 1)e₁ ∈ 𝔓ᵐ⁺¹`.
The product proof expands `gh − 1` and inserts `e₁ + e₂` in the quadratic term.
The inverse proof uses `(g⁻¹ − 1) = −(g − 1) − (g⁻¹ − 1)(g − 1)` and the
same decomposition into products of filtration steps.

This subgroup expresses a deeper `(2,1)` condition of the kind used in the
character transfers of Bushnell–Kutzko, *The admissible dual of GL(N) via compact
open subgroups* (1993), in the proof of (8.2.26), printed p. 288.
