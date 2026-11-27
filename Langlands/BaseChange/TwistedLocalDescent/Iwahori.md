# The Iwahori factorization in additive coordinates

Module `Langlands.BaseChange.TwistedLocalDescent.Iwahori`. Let `𝕂` be an ultrametric, proper,
nontrivially normed field and `B` a block shape.

## The decomposition `M_n = 𝔭 ⊕ 𝔲̄`

- `upperPart_mem`, `lowerPart_mem`, `lowerPart_eq_zero_of_mem`, `lowerPart_eq_self_of_mem`,
  `lowerPart_add`, `upperPart_add_of_mem`, `lowerPart_add_of_mem`, `upperPart_add_lowerPart`.
- `blockSumAddEquiv B : 𝔭 × 𝔲̄ ≃+ M_n`, `(W, Z) ↦ W + Z`, with `blockSumHomeomorph`;
  `norm_add_of_mem`: `‖W + Z‖ = max(‖W‖, ‖Z‖)` (disjoint supports).
- `lowerUnit B Z = 1 + Z ∈ GL_n` for `Z ∈ 𝔲̄`, with inverse `lowerInverse B Z`;
  `continuous_lowerUnit`, `isClosed_lowerLie`.

## Measures

- `blockSumMeasure B νS νL = (νS × νL).map (W, Z ↦ W + Z)` for additive Haar measures on `𝔭` and
  `𝔲̄`; it is an additive Haar measure on `M_n` (`blockSumMeasure_isAddHaarMeasure`), and its
  restriction to `B(0, r)` is the image of `νS|_{B(0,r)} × νL|_{B(0,r)}`
  (`blockSumMeasure_restrict_closedBall_zero`).
- `lipschitzOnWith_upperPart_mul_lowerPart`: `X ↦ X_𝔭 X_𝔲̄` is `r`-Lipschitz on `B(0, r)`;
  `map_restrict_closedBall_perturbation`: for `0 < r < 1`, `X ↦ X + X_𝔭 X_𝔲̄` preserves
  `ν|_{B(0,r)}` (`map_restrict_closedBall_of_perturbation'` with `A = id`).
- `restrict_closedBall_one_eq_map`, `map_one_add_restrict_closedBall_zero`: translation by `1`.
- `map_mul_one_add_restrict` (**Iwahori factorization in coordinates**): for `0 < r < 1`,
  `(νS|_{B(1,r)} × νL|_{B(0,r)}).map ((X, Z) ↦ X (1 + Z)) = ν|_{B(1,r)}`. Writing `X = 1 + W`,
  `(1 + W)(1 + Z) = 1 + (W + Z) + W Z`, and the previous items apply.
