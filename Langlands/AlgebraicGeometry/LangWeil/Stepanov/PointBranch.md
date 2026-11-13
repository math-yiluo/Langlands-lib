# Point branches of a plane curve

Author: Worker 5406. Internal helper for the proof of
`Langlands.AlgebraicGeometry.LangWeil.StepanovNormPolynomialsStatement`; own formalisation
route (see `Branch.md` for the relation to Schmidt's hyperderivatives).

Let `P ∈ F[X][Y]`, `L / F` a field extension and `(x, y) ∈ F × L` with `P(x, y) = 0` and
`P_Y(x, y) ≠ 0`.

## Definitions

- `ev x y : F[X][Y] →+* L`, evaluation at `(x, y)`; `ev_C`, `ev_X`, and `ev_eq`
  (`ev x y A = ((A.map (evalRingHom x)).map (algebraMap F L)).eval y`).
- `rho P x y : F[X][Y] →+* L⟦T⟧`: evaluate the coefficients of the universal branch
  substitution `sigma P` (`Branch.lean`) at `(x, y)` and rescale `S ↦ P_Y(x, y)^(-2) T`.
- `branch P x y = rho P x y Y`.

## Results

- `constantCoeff_subst`, `constantCoeff_sigma`: the constant coefficient of `sigma P A` is `A`.
- `coeff_rho`: the coefficient of `T^l` of `rho P x y A` is
  `(P_Y(x, y)^(-2))^l · ev x y (coeff_l (sigma P A))`; `coeff_zero_rho` (`= A(x, y)`),
  `coeff_zero_branch` (`= y`).
- `rho_self`: `rho P x y P = 0` when `P(x, y) = 0` (from `sigma_self`).
- `rho_comp_C`, `rho_eq`, `rho_apply`: if `P_Y(x, y) ≠ 0`, then `rho P x y` is the substitution
  `X ↦ x + T`, `Y ↦ branch P x y`, i.e. `rho P x y A = A(x + T, branch P x y)`. The rescaling
  turns `X + P_Y² S` into `x + T`.
- `eval_branch`: `branch P x y` is a root of `P(x + T, Y)` in `L⟦T⟧`.
- `X_pow_dvd_pow_sub_C`: in characteristic `p`, `T^(p^k) ∣ Ψ^(p^k) - C(Ψ(0))^(p^k)`.
- `coeff_rho_sum_mul_pow`: for `q = p^k` and `l < q`,
  `coeff_l (rho P x y (∑_i B_i E_i^q)) = (P_Y(x, y)^(-2))^l ∑_i ev x y (coeff_l (sigma P B_i)) · E_i(x, y)^q`.
  This is the formal counterpart of Stepanov's observation that `q`-th powers behave like
  constants under the first `q - 1` derivatives.
- `mul_card_le_rootMultiplicity_of_rho`: if `T ⊆ L` is a finite set of `y` with `P(x, y) = 0`,
  `P_Y(x, y) ≠ 0` and `coeff_l (rho P x y A) = 0` for all `l < M`, and `Res_Y(P, A)` (sizes
  `natDegree P`, `D ≥ natDegree A`) is nonzero, then `M · #T ≤ rootMultiplicity x (Res_Y(P, A))`.
  The branches of distinct `y` are distinct (their constant terms differ), so this follows from
  `mul_card_le_rootMultiplicity_resultant` (`Norm.lean`).
