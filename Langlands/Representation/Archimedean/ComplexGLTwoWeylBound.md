# The Weyl element on highest weight vectors of the `GL_2(ℂ)` principal series

Module `Langlands.Representation.Archimedean.ComplexGLTwoWeylBound`, namespace
`Langlands.Archimedean.ComplexGLTwoNoncompact`. Internal helper module for the proof of
`ComplexGLTwoMomentCompletenessStatement` (see `ComplexGLTwoMomentCompletenessProof`).
Notation as in `ComplexGLTwoHighestWeight`: `φ_b(z) = (1 + |z|²)^(-γ) z̄^b` with
`γ = q + 1 + b`, `m = l_0 - l_1`, `ρ` the right-translation action of `U(2)` and `wU` the Weyl
element `w = [[0, 1], [1, 0]]` of `U(2)`.

## Results

* `ncpL_rho_wU_mul_pw`: if `φ_v = φ_b` and `z ≠ 0`, then
  `φ_{ρ(w) v}(z) (1 + |z|²)^γ = (-1)^(l_0) z^(b - m)` (integer power).
* `weight_sub_le`: if `φ_v = φ_b`, then `m ≤ b`.
* `ncpL_rho_wU_eq`: if `φ_v = φ_b` and `c ∈ ℕ` with `c = b - m`, then
  `φ_{ρ(w) v}(z) = (-1)^(l_0) (1 + |z|²)^(-γ) z^c` for all `z`.

## Proofs

* Helpers: `pw_inv`: `(1 + |1/z|²)^σ = (1 + |z|²)^σ exp(-2σ log|z|)` for `z ≠ 0` (from
  `1 + |z|⁻² = (1 + |z|²)/|z|²`); `exp_log_mul_int`: `exp(k log r) = r^k` for `r > 0`, `k ∈ ℤ`;
  `neg_one_zpow_mul_self`: `(-1)^l (-1)^l = 1`.
* `ncpL_rho_wU_mul_pw`: by `ncpL_rho_wU` and `apply_lowerChart`,
  `φ_{ρ(w) v}(z) = v(1 + z E_10) = φ_b(1/z) / δχ(t)`, where `t = chartTorus 0 1 (1/z)` is
  `diag(-z, 1/z)` and the Library's `principalSeriesCharacter_ofFn` writes `δχ(t)` as the
  product of the two `borelFactor`s. Write `z = r u` with `r = |z|` and `|u| = 1`; then
  `z̄⁻¹ = u / r`, the Borel factors are `(-1)^(l_0) u^(l_0) r^(2 t_0 + 1)` and
  `u^(-l_1) r^(-(2 t_1 - 1))`, and `pw_inv` turns `(1 + |1/z|²)^(-γ)` into
  `(1 + |z|²)^(-γ) r^(2γ)`. After multiplying by `(1 + |z|²)^γ`, the power of `r` is
  `2γ - b - (2 t_0 + 1) + (2 t_1 - 1) = b - m` (since `2γ = 2(t_0 - t_1) - m + 2 + 2b`), the power
  of `u` is `b - m`, and the sign is `(-1)^(l_0)`; so the product is `(-1)^(l_0) z^(b - m)`. In
  Lean the exponentials are combined into one (`hE`), turned into integer powers of `r`
  (`exp_log_mul_int`), and the identity is closed by `field_simp` and `ring` using
  `u^b u^(l_1) = u^(b - m) u^(l_0)`.
* `weight_sub_le`: suppose `m > b` and write `m - b = n + 1`. The continuous function
  `g(z) = φ_{ρ(w) v}(z) (1 + |z|²)^γ z^(n + 1)` equals `(-1)^(l_0)` on `z ≠ 0` by
  `ncpL_rho_wU_mul_pw`, hence everywhere (`Continuous.ext_on`, density of `ℂ ∖ {0}`); but
  `g(0) = 0`, and `(-1)^(l_0) ≠ 0`.
* `ncpL_rho_wU_eq`: on `z ≠ 0`, multiply `ncpL_rho_wU_mul_pw` by `(1 + |z|²)^(-γ)`; both sides
  are continuous, so they agree everywhere.
