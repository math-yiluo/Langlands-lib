# The algebra of the induction step

Module `Langlands.Representation.Shahidi.OpenCellInductionAlgebra`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `shellCoefficient_smul`: `shellCoefficient (w x) D = w^D shellCoefficient x D`;
  `shellCoefficient_eq_zero` beyond the number of variables; `sum_range_pow_mul_shellCoefficient`,
  `hasSum_pow_mul_shellCoefficient`: `∑_D shellCoefficient x D w^D = ∏_p (1 - w x_p)`.
- `sum_threeBlock_identity`: for nonzero `X`, `Z`,

  `∑_(e₁ ≤ d+t+2) X^(e₁) Z^(e₁) ∏_(j,l) (1 - Z a'_j c_l⁻¹ q⁻¹) shellCoefficient (pairParameter q a₁ (Z a', c) 0) e₁
    = ∏_j (1 - X a₁ a'_j⁻¹ q⁻¹) · ∏_(i,l) (1 - Z (X a₁, a')_i c_l⁻¹ q⁻¹)`.

## Provenance

Elementary algebra of elementary symmetric functions.
