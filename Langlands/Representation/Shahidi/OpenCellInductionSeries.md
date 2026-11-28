# The two generating series of the three-block coefficients

Module `Langlands.Representation.Shahidi.OpenCellInductionSeries`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

The results below other than the definitions and the auxiliary `degreePiece_const_mul`,
`jacquetFunction_degreePiece_const_mul`, `baseValue_eq_mul`, `baseValue_of_lt` assume that `ψ`
has conductor `𝒪`.

- `threeCoef ψ hϖ d t a₁ a' c D e₁`: the left side of `jacquetFunction_threeBlock`.
- `threeCoef_eq` (transitivity), `threeCoef_of_neg_left`, `threeCoef_of_neg_right`: vanishing for
  `D < 0` or `e₁ < 0`; `threeCoef_eq_base`: by the rank-one shells,
  `threeCoef D e₁ = baseCoef(e₁) · baseValue(e₁, J_(d+1,t+1)[(fullΦ a' c 0)_(D-e₁)])`;
  `threeCoef_of_lt`: vanishing for `e₁ > d + t + 2`.
- `threeCoef_series_right`: under `CoreAt d t`, for every `e₁ ≥ 0` there is `ρ > 0` such that for
  nonzero `Z` with `‖Z‖ < ρ`,
  `∑_D threeCoef D e₁ Z^D = Z^(e₁) ∏_(j,l) (1 - Z a'_j c_l⁻¹ q⁻¹) ·
  shellCoefficient (pairParameter q a₁ (Z a', c) 0) e₁`, from the graded Shintani identity at the
  torus point `ϖ^(κ(d+1+t, e₁))` and `baseCoef_mul_baseValue`.
- `threeCoef_series_left`: under `CoreAt 0 d`, there is `r₀ > 0` such that for nonzero `X` with
  `‖X‖ < r₀` and every `D`,
  `∑_(e₁) X^(e₁) threeCoef D e₁ = ∏_j (1 - X a₁ a'_j⁻¹ q⁻¹) · J_(d+2,t+1)[(fullΦ (X a₁, a') c 0)_D](1)`,
  from the graded Shintani identity on the first block and termwise summation.

## Provenance

Derived from `Langlands.Representation.Shahidi.OpenCellGraded` and
`Langlands.Representation.Shahidi.OpenCellThreeBlockFubini`.
