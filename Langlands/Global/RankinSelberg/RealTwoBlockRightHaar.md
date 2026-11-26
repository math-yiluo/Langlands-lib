# Real two-block Haar integration with the first block on the right

Notation as in `RealTwoBlockHaar`.

* `diagonalBlocks_mul`, `diagonalBlocks_split`, `diagonalBlocks_conj_upperRectangle`: block
  diagonal matrices multiply blockwise, and conjugation by `diag(g₁, g₂)` sends
  `upperRectangle X` to `upperRectangle (g₁ X g₂⁻¹)`.
* `rightTail g₂ Y q = q · diag(1, g₂) · upperRectangle Y`, and
  `orthogonal_upper_diagonal_eq_rightTail`:
  `q · upperRectangle X · diag(g₁, g₂) = rightTail g₂ (X g₂) q · diag(g₁, 1)`.
* `rightTailWeight g₂ = |det g₂|^{-k}`.
* Continuity and measurability of the chart map (`continuous_rightChart`, `measurable_rightChart`).

`RealTwoBlockRightHaarStatement`: with `μ`, `μ₁`, `μ₂`, `ν`, `κ` as in `RealTwoBlockHaarStatement`
and `ρ = ((μ₁ × μ₂) × rectangularMeasure ν k (n-k)) × κ`, there is `c > 0` with

`μ = c • map ((((g₁, g₂), Y), q) ↦ rightTail g₂ Y q · diag(g₁, 1)) (ρ.withDensity (rightTailWeight g₂))`.

`realTwoBlockRightHaar` proves it: the substitution `Y = X g₂` on the rectangle multiplies the
additive Haar measure by `|det g₂|^{-k}` (the rectangular Haar change of variables
`haarMeasure_map_rectangular` with the absolute value), which Tonelli's theorem inserts as a
density; composing with `realTwoBlockHaar` gives the formula.

This is the real counterpart of the Library's `ComplexTwoBlockRightHaar`, whose density is
`|det g₂|_ℂ^{-k}` with the normalized absolute value `|z|_ℂ = z z̄`, the reciprocal of the `k`-th
power of the normalized absolute determinant. The chart `(g₁, g₂, Y, q) ↦ q · diag(1, g₂) ·
upperRectangle Y · diag(g₁, 1)` with density `|det g₂|^{-k}` is the factorization of Haar measure
printed in Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §10.1 (with the one-column case
in §9.1).
