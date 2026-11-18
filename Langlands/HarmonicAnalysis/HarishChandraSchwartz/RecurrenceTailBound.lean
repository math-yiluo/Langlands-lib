import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeakPartProjection

/-! # Recovering an actual right-finite function from a uniformly bounded tail -/

noncomputable section

namespace Langlands.HarishChandraSchwartz

open Polynomial Langlands.HarmonicAnalysis

/-- An explicit inverse of `X` modulo a polynomial with nonzero constant
coefficient. This form makes its coefficient bound immediate. -/
def inverseXMod (p : ℂ[X]) : ℂ[X] :=
  C (-(p.coeff 0)⁻¹) * p.divX

theorem dvd_X_mul_inverseXMod_sub_one {p : ℂ[X]} (hp : p.coeff 0 ≠ 0) :
    p ∣ X * inverseXMod p - 1 := by
  refine ⟨C (-(p.coeff 0)⁻¹), ?_⟩
  have hc : C (-(p.coeff 0)⁻¹) * C (p.coeff 0) = -1 := by
    rw [← C_mul, neg_mul, inv_mul_cancel₀ hp, C_neg, C_1]
  have h := X_mul_divX_add p
  rw [inverseXMod]
  linear_combination C (-(p.coeff 0)⁻¹) * h - hc

/-- Uniform degree and coefficient bounds, with the constant coefficient
bounded away from zero, also bound the inverse of `X` modulo the polynomial. -/
theorem isCoeffBounded_inverseXMod {p : ℂ[X]} {N : ℕ} {B α : ℝ}
    (hp : IsCoeffBounded p N B) (hα : 0 < α) (hp0 : α ≤ ‖p.coeff 0‖) :
    IsCoeffBounded (inverseXMod p) N (α⁻¹ * B) := by
  refine ⟨(natDegree_C_mul_le _ _).trans (natDegree_divX_le.trans hp.1), ?_⟩
  intro k
  rw [inverseXMod, coeff_C_mul, coeff_divX, norm_mul, norm_neg, norm_inv]
  exact mul_le_mul (inv_anti₀ hα hp0) (hp.2 (k + 1)) (norm_nonneg _)
    (inv_nonneg.mpr hα.le)

/-- A polynomial inverse gives exact recovery from any later power for a
vector annihilated by the original polynomial. -/
theorem aeval_inverseXMod_pow_apply
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (T : Module.End ℂ Y) {p : ℂ[X]} (hp : p.coeff 0 ≠ 0)
    {y : Y} (hy : aeval T p y = 0) (r : ℕ) :
    aeval T (inverseXMod p ^ r) ((T ^ r) y) = y := by
  have hdiv : p ∣ (X * inverseXMod p) ^ r - 1 := by
    have h := dvd_multiset_prod_sub_one
      (p := p) (s := Multiset.replicate r (X * inverseXMod p))
      (fun q hq => by
        obtain rfl := Multiset.eq_of_mem_replicate hq
        exact dvd_X_mul_inverseXMod_sub_one hp)
    simpa only [Multiset.prod_replicate] using h
  have he := aeval_apply_eq_of_dvd T (pw := p) (pp := 1)
    (E := (X * inverseXMod p) ^ r) hdiv (one_dvd _) (x := y) (xw := y) (xp := 0)
    (by simp) hy (by simp)
  rw [mul_pow, mul_comm (X ^ r)] at he
  simpa only [map_mul, map_pow, aeval_X, Module.End.mul_apply] using he

/-- Uniformly bounded polynomial recurrences with nonzero constant
coefficient recover a function from a finite interval arbitrarily far in its
forward tail. The recovery constant is independent of the function and its
annihilator. -/
theorem norm_le_sum_tail_of_aeval_eq_zero
    {G : Type*} [Group G] (a : G) (N r : ℕ) {B α : ℝ}
    (hα : 0 < α) {p : ℂ[X]} (hp : IsCoeffBounded p N B) (hp0 : α ≤ ‖p.coeff 0‖)
    {F : G → ℂ} (hF : aeval (GroupAction.rightFunctions a) p F = 0) (m : G) :
    ‖F m‖ ≤ (((N + 1 : ℕ) : ℝ) * (α⁻¹ * B)) ^ r *
      ∑ i ∈ Finset.range (r * N + 1), ‖F (m * a ^ (r + i))‖ := by
  have hpne : p.coeff 0 ≠ 0 := norm_pos_iff.mp (hα.trans_le hp0)
  have hi := isCoeffBounded_inverseXMod hp hα hp0
  have hq : IsCoeffBounded (inverseXMod p ^ r) (r * N)
      ((((N + 1 : ℕ) : ℝ) * (α⁻¹ * B)) ^ r) := by
    have h := isCoeffBounded_multiset_prod
      (s := Multiset.replicate r (inverseXMod p)) (d := N) (B := α⁻¹ * B)
      (fun q hq => by
        obtain rfl := Multiset.eq_of_mem_replicate hq
        exact hi)
    simpa only [Multiset.prod_replicate, Multiset.card_replicate, Nat.cast_add, Nat.cast_one] using h
  have he := congrFun (aeval_inverseXMod_pow_apply (GroupAction.rightFunctions a) hpne hF r) m
  rw [aeval_eq_sum_range' (n := r * N + 1) (by have := hq.1; omega),
    LinearMap.sum_apply, Finset.sum_apply] at he
  have hpow (i : ℕ) :
      ((GroupAction.rightFunctions a) ^ i) (((GroupAction.rightFunctions a) ^ r) F) m =
        F (m * a ^ (r + i)) := by
    rw [← Module.End.mul_apply, ← pow_add, Nat.add_comm i r,
      ← map_pow, GroupAction.rightFunctions_apply]
  simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hpow] at he
  rw [← he]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hq.2 i) (norm_nonneg _)

end Langlands.HarishChandraSchwartz
