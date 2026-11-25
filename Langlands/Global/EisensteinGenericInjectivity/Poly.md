# Energies along monomial curves are polynomial

Module `Langlands.Global.EisensteinGenericInjectivity.Poly` contains real polynomial algebra
used by the frequency separation of the module
`Langlands.Global.EisensteinGenericInjectivity.Separation`: a quadratic energy evaluated
along a monomial curve `t ↦ ∑_r t^{d_r} y_r` is a polynomial in `t` with an explicit top
coefficient, and a real polynomial with a nonzero coefficient in positive degree takes each value
only finitely often.

All declarations are in the namespace `Langlands.Global.EisensteinGenericInjectivity`. Complete
types are printed by `PrettyPrinter.ppSignature` (the `#check` form), with the namespaces of the
page of `Langlands.Global.EisensteinGenericInjectivity.PlaceHeight` open.

## Declarations

- `energyPoly B y d = ∑_{r,s} C(B(y_r, y_s)) X^{d_r + d_s}`, for a real-valued `B` on pairs of
  vectors of `ℂ^N`, vectors `y_r` and natural exponents `d_r`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.energyPoly {n N : ℕ}
    (B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ) (y : Fin n → Fin N → ℂ) (d : Fin n → ℕ) : Polynomial ℝ
  ```
- `eval_energyPoly`: if `Q(∑_r a_r y_r) = ∑_{r,s} a_r a_s B(y_r, y_s)` for all real `a`, then
  `energyPoly B y d` evaluated at `t` is `Q(∑_r t^{d_r} y_r)`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.eval_energyPoly {n N : ℕ} {Q : (Fin N → ℂ) → ℝ}
    {B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ} {y : Fin n → Fin N → ℂ}
    (hexp : ∀ (a : Fin n → ℝ), Q (∑ r, ↑(a r) • y r) = ∑ r, ∑ s, a r * a s * B (y r) (y s))
    (d : Fin n → ℕ) (t : ℝ) : Polynomial.eval t (energyPoly B y d) = Q (∑ r, ↑(t ^ d r) • y r)
  ```
- `natDegree_energyPoly_le`: if `d_r ≤ D` for all `r`, the degree is at most `2D`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.natDegree_energyPoly_le {n N : ℕ}
    {B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ} {y : Fin n → Fin N → ℂ} {d : Fin n → ℕ} {D : ℕ}
    (hd : ∀ (r : Fin n), d r ≤ D) : (energyPoly B y d).natDegree ≤ 2 * D
  ```
- `coeff_energyPoly_top`: under the expansion hypothesis and `d_r ≤ D`, the coefficient of
  `X^{2D}` is `Q(∑_{r : d_r = D} y_r)`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.coeff_energyPoly_top {n N : ℕ} {Q : (Fin N → ℂ) → ℝ}
    {B : (Fin N → ℂ) → (Fin N → ℂ) → ℝ} {y : Fin n → Fin N → ℂ}
    (hexp : ∀ (a : Fin n → ℝ), Q (∑ r, ↑(a r) • y r) = ∑ r, ∑ s, a r * a s * B (y r) (y s))
    {d : Fin n → ℕ} {D : ℕ} (hd : ∀ (r : Fin n), d r ≤ D) :
    (energyPoly B y d).coeff (2 * D) = Q (∑ r, ↑(if d r = D then 1 else 0) • y r)
  ```
- `coeff_prod_pow_of_natDegree_le`: a finite product `∏_i p_i^{m_i}` with `deg p_i ≤ D_i` has
  degree at most `∑_i m_i D_i`, and its coefficient there is `∏_i (coeff_{D_i} p_i)^{m_i}`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.coeff_prod_pow_of_natDegree_le.{u_1} {«ι» : Type u_1}
    (s : Finset «ι») (p : «ι» → Polynomial ℝ) (m D : «ι» → ℕ) (hp : ∀ i ∈ s, (p i).natDegree ≤ D i) :
    (∏ i ∈ s, p i ^ m i).natDegree ≤ ∑ i ∈ s, m i * D i ∧
      (∏ i ∈ s, p i ^ m i).coeff (∑ i ∈ s, m i * D i) = ∏ i ∈ s, (p i).coeff (D i) ^ m i
  ```
- `finite_setOf_eval_eq`: a real polynomial whose coefficient at some degree `k > 0` is nonzero
  takes each real value `c` only at finitely many points.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.finite_setOf_eval_eq {p : Polynomial ℝ} {k : ℕ}
    (hk : 0 < k) (hc : p.coeff k ≠ 0) (c : ℝ) : {t | Polynomial.eval t p = c}.Finite
  ```

## Proofs

- `eval_energyPoly` and `coeff_energyPoly_top` expand the double sum; only the pairs with
  `d_r + d_s = 2D`, that is `d_r = d_s = D`, contribute to the top coefficient, and the
  expansion hypothesis at the indicator coefficients `a_r = [d_r = D]` identifies the sum.
- `coeff_prod_pow_of_natDegree_le` is an induction on the finite set
  (`Polynomial.coeff_mul_add_eq_of_natDegree_le`, `Polynomial.coeff_pow_of_natDegree_le`).
- `finite_setOf_eval_eq`: `p − C c` is nonzero because its coefficient at `k > 0` is that of
  `p`, and a nonzero polynomial has finitely many roots.

## Sources

Elementary polynomial algebra; no literature source.
