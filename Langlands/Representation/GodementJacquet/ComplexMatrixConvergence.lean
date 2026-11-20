import Langlands.Representation.GodementJacquet.ComplexMatrixHaar
import Langlands.Global.ArchimedeanCharacterGrowth
import Langlands.Global.RankinSelberg.ComplexLocalEqualHolomorphy
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Initial convergence of complex matrix zeta integrals -/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Global.RankinSelbergGlobal
  (complexMatrixHeight differentiableOn_integral_mul_cexp)
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open RankinSelberg.GLDeterminantDensity

local instance matrixZetaGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℂ) := borel _
local instance matrixZetaGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℂ) := ⟨rfl⟩
local instance matrixZetaMatrixBorel (n : ℕ) : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => GeneralLinear n ℂ
local notation "M" => Matrix I I ℂ

private theorem norm_det_le_size (X : M) :
    ‖X.det‖ ≤ (Nat.factorial n : ℝ) * (1 + ‖X‖) ^ n :=
  Langlands.Global.norm_det_le_factorial_mul_pow (Nat.succ_pos _) X _
    (fun _ _ => Matrix.norm_entry_le_entrywise_sup_norm X |>.trans
      (le_add_of_nonneg_left zero_le_one))

private theorem norm_adjugate_entry_le_size (X : M) (i j : I) :
    ‖X.adjugate i j‖ ≤ (Nat.factorial n : ℝ) * (1 + ‖X‖) ^ n := by
  rw [Matrix.adjugate_apply]
  apply Langlands.Global.norm_det_le_factorial_mul_pow (Nat.succ_pos _)
  intro k l
  by_cases hk : k = j
  · subst k
    rw [Matrix.updateRow_self]
    simp only [Pi.single_apply]
    split
    · simpa only [norm_one] using (le_add_of_nonneg_right (norm_nonneg X))
    · simpa only [norm_zero] using (add_nonneg zero_le_one (norm_nonneg X))
  · rw [Matrix.updateRow_ne hk]
    exact Matrix.norm_entry_le_entrywise_sup_norm X |>.trans (le_add_of_nonneg_left zero_le_one)

private theorem norm_det_mul_inv_entry (g : G) (i j : I) :
    ‖g.val.det‖ * ‖(g⁻¹).val i j‖ = ‖g.val.adjugate i j‖ := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply,
    smul_eq_mul, norm_mul, norm_inv, ← mul_assoc,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)), one_mul]

/-- Multiplying the Whittaker height by the positive determinant modulus
cancels its inverse-matrix denominator. The result has polynomial growth
in the additive matrix norm. -/
theorem complexMatrixHeight_mul_det_bound (g : G) :
    complexMatrixHeight g * complexNormalizedAbs g.val.det ≤
      (2 * (n : ℝ) ^ 2 * (Nat.factorial n : ℝ) ^ 2) * (1 + ‖g.val‖) ^ (2 * (n + 1)) := by
  let X := g.val
  let P := 1 + ‖X‖
  let F := (Nat.factorial n : ℝ)
  have hP : 1 ≤ P := le_add_of_nonneg_right (norm_nonneg _)
  have hF : 0 ≤ F := Nat.cast_nonneg _
  have hDet : ‖X.det‖ ≤ F * P ^ n := norm_det_le_size X
  have hB (i j : I) : ‖X i j‖ ≤ P :=
    Matrix.norm_entry_le_entrywise_sup_norm X |>.trans (le_add_of_nonneg_left zero_le_one)
  have hmain (i j : I) : ‖X i j‖ * ‖X.det‖ ≤ F * P ^ (n + 1) := by
    rw [pow_succ, ← mul_assoc, mul_comm _ P]
    exact mul_le_mul (hB i j) hDet (norm_nonneg _) (zero_le_one.trans hP)
  have hadj (i j : I) : ‖X.adjugate i j‖ ≤ F * P ^ (n + 1) := by
    refine (norm_adjugate_entry_le_size X i j).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP (by omega)) hF)
  unfold complexMatrixHeight complexNormalizedAbs
  simp only [Finset.sum_mul, add_mul]
  calc
    _ ≤ ∑ _i : I, ∑ _j : I, ((F * P ^ (n + 1)) ^ 2 + (F * P ^ (n + 1)) ^ 2) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      change ‖X i j‖ ^ 2 * ‖X.det‖ ^ 2 + ‖(g⁻¹).val i j‖ ^ 2 * ‖X.det‖ ^ 2 ≤ _
      rw [← mul_pow, ← mul_pow, mul_comm ‖(g⁻¹).val i j‖,
        norm_det_mul_inv_entry g i j]
      exact add_le_add (pow_le_pow_left₀ (by positivity) (hmain i j) _)
        (pow_le_pow_left₀ (norm_nonneg _) (hadj i j) _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_pow,
        ← pow_mul, mul_comm (n + 1) 2, F, P, X]
      push_cast
      ring

private theorem exists_height_detPower_bound (N : ℕ) (s : ℝ)
    (hs : (n : ℝ) + N ≤ s) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧ ∀ g : G,
      complexMatrixHeight g ^ N * complexNormalizedAbs g.val.det ^ (s - (n : ℝ)) ≤
        C * (1 + ‖g.val‖) ^ p := by
  let K : ℝ := 2 * (n : ℝ) ^ 2 * (Nat.factorial n : ℝ) ^ 2
  let F : ℝ := (Nat.factorial n : ℝ) ^ 2
  let t := s - (n : ℝ) - N
  let b := ⌈t⌉₊
  have ht : 0 ≤ t := by dsimp [t]; linarith
  refine ⟨K ^ N * (1 + F) ^ b, (2 * (n + 1)) * N + (2 * n) * b, by positivity, fun g => ?_⟩
  let A := complexNormalizedAbs g.val.det
  let P := 1 + ‖g.val‖
  have hA : 0 < A := pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) _
  have hP : 1 ≤ P := le_add_of_nonneg_right (norm_nonneg _)
  have hF : 0 ≤ F := sq_nonneg _
  have hAdet : A ≤ F * P ^ (2 * n) := by
    rw [mul_comm 2 n, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_det_le_size g.val) 2
  have hb : 1 + A ≤ (1 + F) * P ^ (2 * n) := by
    rw [add_mul, one_mul]
    exact add_le_add (one_le_pow₀ hP) hAdet
  have hDr : A ^ t ≤ ((1 + F) * P ^ (2 * n)) ^ b := by
    calc
      _ ≤ (1 + A) ^ t := Real.rpow_le_rpow hA.le (le_add_of_nonneg_left zero_le_one) ht
      _ ≤ (1 + A) ^ (b : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right hA.le) (Nat.le_ceil _)
      _ ≤ _ := by
        rw [Real.rpow_natCast]
        exact pow_le_pow_left₀ (add_nonneg zero_le_one hA.le) hb _
  have hprod : 0 ≤ complexMatrixHeight g * A := by
    exact mul_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      add_nonneg (sq_nonneg _) (sq_nonneg _)) hA.le
  calc
    _ = (complexMatrixHeight g * A) ^ N * A ^ t := by
      rw [mul_pow, mul_assoc, ← Real.rpow_natCast A N, ← Real.rpow_add hA]
      rw [show (N : ℝ) + t = s - (n : ℝ) by dsimp [t]; ring]
    _ ≤ (K * P ^ (2 * (n + 1))) ^ N * ((1 + F) * P ^ (2 * n)) ^ b :=
      mul_le_mul (pow_le_pow_left₀ hprod (complexMatrixHeight_mul_det_bound g) _) hDr
        (Real.rpow_nonneg hA.le _) (by positivity)
    _ = _ := by
      change (K * P ^ (2 * (n + 1))) ^ N * ((1 + F) * P ^ (2 * n)) ^ b =
        K ^ N * (1 + F) ^ b * P ^ (2 * (n + 1) * N + 2 * n * b)
      rw [mul_pow K, mul_pow (1 + F), mul_mul_mul_comm, ← pow_mul P, ← pow_mul P, ← pow_add]

private theorem integrable_schwartz_norm_mul_one_add_pow (μ : Measure M) [μ.IsAddHaarMeasure]
    (Φ : SchwartzMap M ℂ) (p : ℕ) :
    Integrable (fun X => (1 + ‖X‖) ^ p * ‖Φ X‖) μ := by
  let : FiniteDimensional ℝ M := inferInstanceAs (FiniteDimensional ℝ (I → I → ℂ))
  have h0 : Integrable (fun X => ‖Φ X‖) μ := Φ.integrable.norm
  have hp := Φ.integrable_pow_mul μ p
  have hi := (h0.add hp).const_mul (2 ^ p : ℝ)
  refine hi.mono' (((continuous_const.add continuous_norm).pow _).mul
    Φ.continuous.norm).aestronglyMeasurable (ae_of_all _ fun X => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  change (1 + ‖X‖) ^ p * ‖Φ X‖ ≤ (2 : ℝ) ^ p * (‖Φ X‖ + ‖X‖ ^ p * ‖Φ X‖)
  have hnorm : (1 + ‖X‖) ^ p ≤ (2 : ℝ) ^ p * (1 + ‖X‖ ^ p) := by
    rcases le_total ‖X‖ 1 with hx | hx
    · exact (pow_le_pow_left₀ (by positivity) (by linarith) p).trans
        (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (pow_nonneg (norm_nonneg _) _)))
    · calc
        _ ≤ (2 * ‖X‖) ^ p := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ ≤ _ := by rw [mul_pow]; gcongr; exact le_add_of_nonneg_left zero_le_one
  calc
    _ ≤ (2 : ℝ) ^ p * (1 + ‖X‖ ^ p) * ‖Φ X‖ :=
      mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    _ = _ := by ring

private theorem norm_weightedMatrixKernel (g : G) (f : G → ℂ) (Φ : SchwartzMap M ℂ) (s : ℂ) :
    ‖(matrixWeight n complexAbsHom g.val : ℝ) •
      (Φ g.val * f g * detPower complexNormalizedAbs g s)‖ =
      ‖Φ g.val‖ * ‖f g‖ * complexNormalizedAbs g.val.det ^ (s.re - (n : ℝ)) := by
  let A := complexNormalizedAbs g.val.det
  have hA : 0 < A := pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) _
  have hw : (matrixWeight n complexAbsHom g.val : ℝ) = A ^ (-(n : ℝ)) := by
    rw [show (n : ℝ) = ↑(r + 1 : ℕ) by norm_cast, Real.rpow_neg hA.le, Real.rpow_natCast]
    simp only [matrixWeight, NNReal.coe_pow, NNReal.coe_inv, coe_complexAbsHom,
      A, complexNormalizedAbs, inv_pow]
  have hdet : ‖detPower complexNormalizedAbs g s‖ = A ^ s.re := by
    rw [Real.rpow_def_of_pos hA, detPower, Complex.norm_exp, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_comm, A]
  rw [norm_smul, Real.norm_of_nonneg (NNReal.coe_nonneg _), norm_mul, norm_mul, hw, hdet]
  change _ = ‖Φ g.val‖ * ‖f g‖ * A ^ (s.re - (n : ℝ))
  rw [sub_eq_add_neg, Real.rpow_add hA]
  ring

/-- A measurable coefficient of polynomial height growth gives an absolutely
convergent matrix zeta kernel for a sufficiently large determinant exponent. -/
theorem integrable_complexMatrixZetaKernel (μ : Measure M) [μ.IsAddHaarMeasure]
    {f : G → ℂ} (hf : Measurable f) (Φ : SchwartzMap M ℂ)
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hbound : ∀ g, ‖f g‖ ≤ C * complexMatrixHeight g ^ N)
    {s : ℂ} (hs : (n : ℝ) + N ≤ s.re) :
    Integrable (fun g => Φ g.val * f g * detPower complexNormalizedAbs g s)
      (complexMatrixHaar n μ) := by
  obtain ⟨K, p, hK, hmajor⟩ := exists_height_detPower_bound (r := r) N s.re hs
  let val : G → M := Units.val
  have he := (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).measurableEmbedding
  let F : M → ℂ := Function.extend val f (fun _ => 0)
  have hF : Measurable F := he.measurable_extend hf measurable_const
  have hF_val (g : G) : F g.val = f g := he.injective.extend_apply _ _ _
  let B (X : M) := Complex.exp (s * (Real.log (complexNormalizedAbs X.det) : ℂ))
  have hB : Measurable B :=
    Complex.continuous_exp.measurable.comp (measurable_const.mul
      (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp
        (continuous_id.matrix_det.norm.pow 2).measurable)))
  let J (X : M) := Φ X * F X * B X
  have hJ : Measurable J := (Φ.continuous.measurable.mul hF).mul hB
  have hJ_val (g : G) : J g.val = Φ g.val * f g * detPower complexNormalizedAbs g s := by
    simp only [J, hF_val, B, detPower]
  simp_rw [← hJ_val]
  apply (integrable_weightedRestriction_iff n complexAbsHom continuous_complexAbsHom μ J).2
  have hWeight : Measurable (fun X : M => (matrixWeight n complexAbsHom X : ℝ)) :=
    NNReal.continuous_coe.measurable.comp (measurable_matrixWeight n complexAbsHom continuous_complexAbsHom)
  refine (((integrable_schwartz_norm_mul_one_add_pow μ Φ p).const_mul (C * K)).mono_measure
    Measure.restrict_le_self).mono' (hWeight.smul hJ).aestronglyMeasurable ?_
  apply (ae_restrict_iff' he.measurableSet_range).2
  refine ae_of_all _ fun X hX => ?_
  obtain ⟨g, rfl⟩ := hX
  change ‖(matrixWeight n complexAbsHom g.val : ℝ) • J g.val‖ ≤ _
  rw [hJ_val, norm_weightedMatrixKernel]
  have hA : 0 ≤ complexNormalizedAbs g.val.det := sq_nonneg _
  calc
    _ ≤ ‖Φ g.val‖ * (C * complexMatrixHeight g ^ N) *
        complexNormalizedAbs g.val.det ^ (s.re - (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbound g) (norm_nonneg _))
        (Real.rpow_nonneg hA _)
    _ = (C * ‖Φ g.val‖) *
        (complexMatrixHeight g ^ N * complexNormalizedAbs g.val.det ^ (s.re - (n : ℝ))) := by ring
    _ ≤ (C * ‖Φ g.val‖) * (K * (1 + ‖g.val‖) ^ p) :=
      mul_le_mul_of_nonneg_left (hmajor g) (mul_nonneg hC (norm_nonneg _))
    _ = _ := by ring

/-- The complex matrix zeta integral, with the shift `(n - 1) / 2` of the
standard Godement–Jacquet normalization. -/
def complexMatrixZeta (μ : Measure M) (f : G → ℂ) (Φ : SchwartzMap M ℂ) (s : ℂ) : ℂ :=
  ∫ g, Φ g.val * f g * detPower complexNormalizedAbs g (s + (r : ℂ) / 2) ∂complexMatrixHaar n μ

/-- The Godement–Jacquet integral of a polynomially bounded coefficient
is holomorphic on its initial right half-plane. -/
theorem differentiableOn_complexMatrixZeta (μ : Measure M) [μ.IsAddHaarMeasure]
    {f : G → ℂ} (hf : Measurable f) (Φ : SchwartzMap M ℂ)
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hbound : ∀ g, ‖f g‖ ≤ C * complexMatrixHeight g ^ N) :
    DifferentiableOn ℂ (complexMatrixZeta μ f Φ) {s : ℂ | (n : ℝ) + N < s.re + (r : ℝ) / 2} := by
  let B (g : G) := Real.log (complexNormalizedAbs (Matrix.det g.val))
  have hB : Measurable B :=
    Real.measurable_log.comp ((continuous_norm.pow 2).comp
      (Units.continuous_val.comp Matrix.GeneralLinearGroup.continuous_det)).measurable
  have hZ : DifferentiableOn ℂ (fun s : ℂ =>
      ∫ g, Φ g.val * f g * Complex.exp (s * (B g : ℂ)) ∂complexMatrixHaar n μ)
      {s : ℂ | (n : ℝ) + N < s.re} :=
    differentiableOn_integral_mul_cexp hB (isOpen_lt continuous_const Complex.continuous_re)
      (fun s hs => integrable_complexMatrixZetaKernel μ hf Φ hC hbound
        (show (n : ℝ) + N < s.re from hs).le)
  have ha : Differentiable ℂ (fun s : ℂ => s + (r : ℂ) / 2) := differentiable_id.add_const _
  exact hZ.comp ha.differentiableOn fun s hs => by
    change (n : ℝ) + N < (s + (r : ℂ) / 2).re
    have hreal : (r : ℂ) / 2 = (((r : ℝ) / 2 : ℝ) : ℂ) := by push_cast; rfl
    rwa [hreal, Complex.add_re, Complex.ofReal_re]

end Langlands.GodementJacquet
