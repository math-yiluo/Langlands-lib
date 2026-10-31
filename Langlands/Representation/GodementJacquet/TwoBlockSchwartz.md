# Upper-block integrals of full-matrix test functions

Module `Langlands.Representation.GodementJacquet.TwoBlockSchwartz`. Author: Worker 1112.

Notation as in `TwoBlockParabolicHaar`: blocks of sizes `n₀ = m 0 + 1`,
`n₁ = m 1 + 1`, block convention `blockEquiv h`, parameters
`parabolicPoint h (L, x)` with matrix `[[a, a x], [0, d]]` for `L = (a, d)`.

## Block maps (any commutative ring)

- `upperBlockMap h ((A, D), B) = Matrix.reindex (blockEquiv h) (blockEquiv h)
  (Matrix.fromBlocks A B 0 D)`, the upper block-triangular matrix `[[A, B], [0, D]]`.
- `upperBlockCoord h X` reads off `((A, D), B)` from the reindexed blocks
  (`toBlocks₁₁`, `toBlocks₂₂`, `toBlocks₁₂`); `upperBlockCoord_upperBlockMap` shows
  it is a left inverse. Both maps are continuous over a topological ring
  (`continuous_upperBlockMap`, `continuous_upperBlockCoord`).
- `parabolicPoint_val_eq_upperBlockMap`: the matrix of `parabolicPoint h (L, x)` is
  `upperBlockMap h (((L 0).val, (L 1).val), (L 0).val * x)`.

## Test functions (Hausdorff topological field `K`)

- `upperBlockRestriction h Φ ∈ SchwartzBruhat ((Mat_{n₀} × Mat_{n₁}) × Mat_{n₀×n₁})`
  is `((A, D), B) ↦ Φ [[A, B], [0, D]]` (via `SchwartzBruhat.compLeftInverse`).
- `upperBlockIntegral h Φ dx ∈ SchwartzBruhat (Mat_{n₀} × Mat_{n₁})` is
  `Φ^P (A, D) = ∫ B, Φ (Matrix.reindex (blockEquiv h) (blockEquiv h)
  (Matrix.fromBlocks A B 0 D)) ∂dx` (`upperBlockIntegral_apply`), for any measure
  `dx` finite on compact sets (via `SchwartzBruhat.partialIntegral`).
- `exists_upperBlockIntegral_expansion`: `Φ^P (A, D) = ∑ j, Ψ₀ j A * Ψ₁ j D` for
  finitely many Schwartz–Bruhat `Ψ₀ j` on `Mat_{n₀}` and `Ψ₁ j` on `Mat_{n₁}`
  (`SchwartzBruhat.exists_tensor_expansion`).

## Two-coordinate products

`integrable_pi_two_mul` and `integral_pi_two_mul`: for σ-finite measures `μ i` on a
family indexed by `Fin 2`, `L ↦ f₀ (L 0) * f₁ (L 1)` is integrable for
`Measure.pi μ` when both factors are, and its integral is the product of the
integrals (`measurePreserving_piFinTwo`, `Integrable.mul_prod`, `integral_prod_mul`).

## Parabolic reduction (canonical p-adic field)

`radicalWeight F h L = |det a|^(-n₁)` (as a complex number, with
`F.canonicalTopologicalData.determinantNorm`).

`integral_testFunction_parabolicPoint`: let `dx` be an additive Haar measure on
`n₀ × n₁` matrices, `Φ` a full-matrix test function and `U` an a.e.-strongly
measurable function on the Levi. Assume that for every Schwartz–Bruhat `α` on
`Mat_{n₀} × Mat_{n₁}` the function `L ↦ α (a, d) * (U L * |det a|^(-n₁))` is
integrable for the product of the normalized block Haar measures. Then
`z ↦ Φ (parabolicPoint z) * U z.1` is integrable for `parabolicMeasure F h dx`, and

`∫ z, Φ (parabolicPoint z) * U z.1 = ∫ L, Φ^P (a, d) * (U L * |det a|^(-n₁))`.

Proof: expand `upperBlockRestriction h Φ = ∑ j, α j ⊗ β j`. Then
`Φ (parabolicPoint (L, x)) = ∑ j, α j (a, d) * β j (a x)`. For each `j` the
function `(L, x) ↦ α j (a, d) U L * β j (a x)` is integrable by
`integrable_prod_iff`: each slice is integrable by the radical scaling lemma
`integrable_mul_left_radical_iff`, and the integral of the norm of the slice is
`‖α j (a, d) U L‖ |det a|^(-n₁) ∫ ‖β j‖` (`integral_mul_left_radical`), which is
integrable by the hypothesis for `α j`. Fubini and the radical scaling give
`∫ α j (a, d) U L |det a|^(-n₁) ∫ β j`, and summing over `j` reassembles
`Φ^P (a, d) = ∑ j, α j (a, d) ∫ β j`.

## Provenance and scope

This is the step of Godement–Jacquet 1972, Theorem 3.4 (printed 40–41) in which
the integral over the parabolic is written as an integral over the Levi of the
unipotent integral of the test function, with the modulus factor coming from the
change of variables `b = a x` on the radical; here the factor `|det a|^(-n₁)`
appears explicitly. The convention for `Φ^P` agrees with the block-matrix
convention `Matrix.reindex e e (Matrix.fromBlocks A B C D)`,
`e = finSumFinEquiv.trans (finCongr (blockRanks_add h))`, used by the
functional-equation task.
