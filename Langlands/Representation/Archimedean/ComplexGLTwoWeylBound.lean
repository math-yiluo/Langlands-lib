import Langlands.Representation.Archimedean.ComplexGLTwoHighestWeight

/-!
# The Weyl element on highest weight vectors of the `GL_2(ℂ)` principal series

Let `v ∈ X(d)` have noncompact picture `φ_b(z) = (1 + |z|²)^(-γ) z̄^b`, `γ = q + 1 + b`, and
let `m = l_0 - l_1`. For `z ≠ 0`,
`φ_{ρ(w) v}(z) (1 + |z|²)^γ = (-1)^(l_0) z^(b - m)` (`ncpL_rho_wU_mul_pw`): by
`ncpL_rho_wU` and `apply_lowerChart` the left side is `φ_b(1/z) / δχ(diag(-z, 1/z))`, and
both factors are explicit. Continuity of `φ_{ρ(w) v}` at `0` gives `m ≤ b`
(`weight_sub_le`), and then `φ_{ρ(w) v}(z) = (-1)^(l_0) (1 + |z|²)^(-γ) z^(b - m)` for all
`z` (`ncpL_rho_wU_eq`).
-/

noncomputable section

open scoped TensorProduct Matrix

open Complex ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

open scoped Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace ComplexGLTwoNoncompact

/-- `(1 + |z|⁻²)^σ = (1 + |z|²)^σ |z|^(-2σ)`. -/
theorem pw_inv (σ : ℂ) {z : ℂ} (hz : z ≠ 0) :
    pw σ z⁻¹ = pw σ z * Complex.exp ((Real.log ‖z‖ : ℂ) * (-2 * σ)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h1 : Real.log (1 + ‖z⁻¹‖ ^ 2) = Real.log (1 + ‖z‖ ^ 2) - 2 * Real.log ‖z‖ := by
    have h2 : 1 + ‖z⁻¹‖ ^ 2 = (1 + ‖z‖ ^ 2) / ‖z‖ ^ 2 := by
      rw [norm_inv]
      field_simp
      ring
    rw [h2, Real.log_div (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [pw, pw, h1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem exp_log_mul_int {r : ℝ} (hr : 0 < r) (k : ℤ) :
    Complex.exp ((Real.log r : ℂ) * (k : ℂ)) = (r : ℂ) ^ k := by
  rw [mul_comm, Complex.exp_int_mul, ← Complex.ofReal_exp, Real.exp_log hr]

theorem neg_one_zpow_mul_self (l : ℤ) : ((-1 : ℂ) ^ l) * (-1) ^ l = 1 := by
  rw [← mul_zpow, neg_one_mul, neg_neg, one_zpow]

variable {d : Fin 2 → ComplexCharacterData}

/-- `φ_{ρ(w) v}(z) (1 + |z|²)^(q + 1 + b) = (-1)^(l_0) z^(b - m)` for `z ≠ 0`. -/
theorem ncpL_rho_wU_mul_pw {v : Xd d} {b : ℕ} (hv : ncpL d v = phiB d b) {z : ℂ} (hz : z ≠ 0) :
    ncpL d (complexStandardRep 2 (List.ofFn d) wU v) z * pw (qq d + 1 + b) z =
      (-1) ^ (d 0).weight * z ^ ((b : ℤ) - ((d 0).weight - (d 1).weight)) := by
  have hf := ComplexSwapJacquet.mem_of_mem_kFs v.2
  rw [ncpL_rho_wU, apply_lowerChart hf z hz]
  change ncpL d v z⁻¹ / _ * _ = _
  rw [hv, phiB, principalSeriesCharacter_ofFn, Fin.prod_univ_two, pw_inv _ hz]
  simp only [ComplexSwapJacquet.chartTorus, ite_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one,
    ite_false, Units.val_neg, Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv, Fin.val_zero,
    Fin.val_one, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero, sub_zero, mul_one]
  have hpp : pw (-(qq d + 1 + b)) z * pw (qq d + 1 + b) z = 1 := by
    rw [← pw_add, neg_add_cancel, pw_zero]
  generalize pw (-(qq d + 1 + b)) z = P at hpp ⊢
  generalize pw (qq d + 1 + b) z = P' at hpp ⊢
  set r : ℝ := ‖z‖ with hr_def
  set L : ℝ := Real.log r with hL_def
  have hr : 0 < r := norm_pos_iff.mpr hz
  have hR : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  set w : ℂ := z / (r : ℂ) with hw_def
  have hw : w ≠ 0 := div_ne_zero hz hR
  have hzw : z = (r : ℂ) * w := by rw [hw_def, mul_div_cancel₀ _ hR]
  have hB0 : ∀ α : ℂ, borelFactor (d 0).weight α (-z) =
      (-1) ^ (d 0).weight * w ^ (d 0).weight * Complex.exp ((L : ℂ) * α) := by
    intro α
    rw [borelFactor, norm_neg, ← hr_def, ← hL_def, neg_div, ← hw_def, neg_eq_neg_one_mul,
      mul_zpow]
  have hB1 : ∀ α : ℂ, borelFactor (d 1).weight α z⁻¹ =
      (w ^ (d 1).weight)⁻¹ * Complex.exp ((L : ℂ) * (-α)) := by
    intro α
    rw [borelFactor, norm_inv, ← hr_def, Real.log_inv, ← hL_def]
    have h : z⁻¹ / ((r⁻¹ : ℝ) : ℂ) = w⁻¹ := by
      rw [hw_def, Complex.ofReal_inv]
      ring
    rw [h, inv_zpow]
    push_cast
    ring_nf
  have hconj : conj z⁻¹ = w / (r : ℂ) := by
    have h1 : z * conj z = (r : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hr_def]
      push_cast
      ring
    have hc : conj z ≠ 0 := (map_ne_zero _).mpr hz
    rw [map_inv₀, hw_def]
    field_simp
    linear_combination -h1
  rw [hB0, hB1, hconj]
  have hE : Complex.exp ((L : ℂ) * (-2 * -(qq d + 1 + b))) =
      Complex.exp ((L : ℂ) * (((b : ℤ) - ((d 0).weight - (d 1).weight) : ℤ) : ℂ)) *
        Complex.exp ((L : ℂ) * ((b : ℤ) : ℂ)) *
        (Complex.exp ((L : ℂ) * (2 * (d 0).exponent + (2 - 1))) *
          Complex.exp ((L : ℂ) * (-(2 * (d 1).exponent + (2 - 1) - 2)))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold qq
    push_cast
    ring
  rw [hE, hL_def, exp_log_mul_int hr, exp_log_mul_int hr, zpow_natCast, hzw, mul_zpow]
  have hwrel : w ^ b * w ^ (d 1).weight =
      w ^ ((b : ℤ) - ((d 0).weight - (d 1).weight)) * w ^ (d 0).weight := by
    rw [← zpow_natCast, ← zpow_add₀ hw, ← zpow_add₀ hw]
    congr 1
    ring
  have hN := neg_one_zpow_mul_self (d 0).weight
  have h0 : w ^ (d 0).weight ≠ 0 := zpow_ne_zero _ hw
  have h1 : w ^ (d 1).weight ≠ 0 := zpow_ne_zero _ hw
  have hN0 : ((-1 : ℂ) ^ (d 0).weight) ≠ 0 := zpow_ne_zero _ (by norm_num)
  field_simp
  rw [div_pow, show P * (r : ℂ) ^ b * (w ^ b / (r : ℂ) ^ b) * w ^ (d 1).weight * P' =
      (P * P') * (w ^ b * w ^ (d 1).weight) * ((r : ℂ) ^ b / (r : ℂ) ^ b) by ring,
    hpp, hwrel, div_self (pow_ne_zero _ hR), sq, hN]
  ring

/-- A vector with noncompact picture `φ_b` has `l_0 - l_1 ≤ b`. -/
theorem weight_sub_le {v : Xd d} {b : ℕ} (hv : ncpL d v = phiB d b) :
    (d 0).weight - (d 1).weight ≤ b := by
  by_contra hlt
  push Not at hlt
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((d 0).weight - (d 1).weight) - b = n + 1 :=
    ⟨((d 0).weight - (d 1).weight - b - 1).toNat, by omega⟩
  set g : ℂ → ℂ := fun z => ncpL d (complexStandardRep 2 (List.ofFn d) wU v) z *
      pw (qq d + 1 + b) z * z ^ (n + 1) with hg
  have hcont : Continuous g :=
    ((differentiable_ncpL _).continuous.mul (continuous_pw _)).mul (continuous_pow _)
  have heq : ∀ z : ℂ, z ≠ 0 → g z = (-1) ^ (d 0).weight := by
    intro z hz
    simp only [hg]
    rw [ncpL_rho_wU_mul_pw hv hz, mul_assoc, ← zpow_natCast, ← zpow_add₀ hz]
    have : (b : ℤ) - ((d 0).weight - (d 1).weight) + ((n + 1 : ℕ) : ℤ) = 0 := by
      push_cast
      omega
    rw [this, zpow_zero, mul_one]
  have hF := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hcont continuous_const heq
  have h0 := congrFun hF 0
  simp only [hg] at h0
  rw [zero_pow (Nat.succ_ne_zero n), mul_zero] at h0
  exact zpow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0) h0.symm

/-- If `c = b - (l_0 - l_1)`, then `φ_{ρ(w) v}(z) = (-1)^(l_0) (1 + |z|²)^(-(q + 1 + b)) z^c`. -/
theorem ncpL_rho_wU_eq {v : Xd d} {b c : ℕ} (hv : ncpL d v = phiB d b)
    (hc : (c : ℤ) = b - ((d 0).weight - (d 1).weight)) :
    ncpL d (complexStandardRep 2 (List.ofFn d) wU v) =
      fun z => (-1) ^ (d 0).weight * pw (-(qq d + 1 + b)) z * z ^ c := by
  apply Continuous.ext_on (dense_compl_singleton (0 : ℂ)) (differentiable_ncpL _).continuous
    ((continuous_const.mul (continuous_pw _)).mul (continuous_pow _))
  intro z hz
  have h := ncpL_rho_wU_mul_pw hv hz
  rw [← hc, zpow_natCast] at h
  have hp : pw (qq d + 1 + b) z * pw (-(qq d + 1 + b)) z = 1 := by
    rw [← pw_add, add_neg_cancel, pw_zero]
  calc ncpL d (complexStandardRep 2 (List.ofFn d) wU v) z
      = ncpL d (complexStandardRep 2 (List.ofFn d) wU v) z * pw (qq d + 1 + b) z *
          pw (-(qq d + 1 + b)) z := by rw [mul_assoc, hp, mul_one]
    _ = _ := by rw [h]; simp only [Pi.mul_apply]; ring

end ComplexGLTwoNoncompact

end Langlands.Archimedean
