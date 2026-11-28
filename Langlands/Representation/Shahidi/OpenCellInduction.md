# The shell identities at `s = 0` for all ranks

Module `Langlands.Representation.Shahidi.OpenCellInduction`, namespace
`Langlands.Shahidi.OpenCell`.

## Contents

- `isPolynomialFn_append`, `prod_append_val`, `isLaurentFn_satakeSchur_append`,
  `isLaurentFn_sphericalWhittaker_append`: for fixed `g`, `X ↦ W°(g; (X a₁, a'))` is a Laurent
  polynomial (the Library's `satakeSchur` is a power of the product of the parameters times a
  Jacobi–Trudi polynomial); `liftPoint₁`, `liftPoint₂`, `liftFunction_eq_liftPoint`.
- `isLaurentFn_shellSum` (for `ψ` of conductor `𝒪`), `isPolynomialFn_shellCoefficient`: the
  shell sum
  `P_D(X) = J[(fullΦ (X a₁, a') c 0)_D](1)` is a Laurent polynomial and
  `T_D(X) = shellCoefficient (pairParameter q (X a₁, a') c 0) D` a polynomial in `X`.
For `ψ` of conductor `𝒪`:
- `coreAt_step`: `CoreAt 0 d → CoreAt d t → CoreAt (d + 1) t` (stated for the rank `0 + 1 + d`).
- `coreAt_zero`: `CoreAt 0 t`, from `shellIdentity_rankOne` and `shellIdentity_iff`.
- `coreAt_all`: `CoreAt r t` for all `r`, `t`.

## Proof of the step

Write `a = (a₁, a')`. For small nonzero `X` and `Z`, multiply the series of
`threeCoef_series_right` by `X^(e₁)` and add over `0 ≤ e₁ ≤ d + t + 2` (all other `e₁`
contribute zero); by `sum_threeBlock_identity` the total is
`∏_j (1 - X a₁ a'_j⁻¹ q⁻¹) ∏ (1 - Z pairParameter q (X a₁, a') c 0)`. Exchanging the finite sum
over `e₁` with the series in `D` and using `threeCoef_series_left`, the coefficient of `Z^D` is
`∏_j (1 - X a₁ a'_j⁻¹ q⁻¹) P_D(X)`; the expansion of the product gives
`∏_j (1 - X a₁ a'_j⁻¹ q⁻¹) T_D(X)`. Uniqueness of power-series coefficients in `Z`
(`eq_of_hasSum_pow`) and `∏_j (1 - X a₁ a'_j⁻¹ q⁻¹) ≠ 0` for small `X` give `P_D(X) = T_D(X)` for
all small nonzero `X`. Both sides are Laurent polynomials in `X`, so they agree at `X = 1`.

## Provenance

Derived; the induction on the rank of the first block via the three-block transitivity is the
implemented route to the two-block value `∏_(i,j) (1 − a_i c_j⁻¹ q^(−(1+s)))` (Shahidi's
normalization, in which the inducing Whittaker functions take the value `1` at the identity, so
that only the roots crossing the two blocks contribute).
