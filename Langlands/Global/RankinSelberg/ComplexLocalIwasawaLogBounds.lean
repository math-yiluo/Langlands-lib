import Langlands.Global.RankinSelberg.ComplexLocalOrdinaryConvergence

/-! # Bounds for the complex Iwasawa logarithms -/

noncomputable section

open Langlands.Archimedean Langlands.RankinSelberg
open scoped Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexLocalIwasawa

open ArchimedeanLocal
open ComplexLocalWhittakerGauge (logTorus)
open ComplexLocalOrdinaryConvergence (norm_detPower_logTorus_mul)

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs

private theorem norm_entry_le_operator (X : Mat) (i j : Fin n) : ‖X i j‖ ≤ ‖X‖ := by
  rw [Matrix.linfty_opNorm_def]
  exact_mod_cast (Finset.single_le_sum (f := fun l => ‖X i l‖₊)
    (fun _ _ => bot_le) (Finset.mem_univ j)).trans
    (Finset.le_sup (f := fun l => ∑ t : Fin n, ‖X l t‖₊) (Finset.mem_univ i))

theorem norm_detPower_eq_exp_alpha (g : G) (s : ℂ) :
    ‖P g s‖ = Real.exp (2 * s.re * ∑ j, alpha g j) := by
  let h := logTorus (alpha g) * (kpart g).val
  have he : (npart g).val * h = g := by
    rw [← mul_assoc]
    exact npart_mul_logTorus_mul_kpart g
  have hd : h.val.det = g.val.det := by
    have hd' := congrArg (fun x : G => x.val.det) he
    simpa only [Units.val_mul, Matrix.det_mul, unipotent_det (npart g), one_mul] using hd'
  calc
    _ = ‖P h s‖ := by rw [ArchimedeanLocal.detPower, ArchimedeanLocal.detPower, hd]
    _ = _ := norm_detPower_logTorus_mul (alpha g) (kpart g) s

theorem complexNormalizedAbs_det_eq_exp_alpha (g : G) :
    complexNormalizedAbs g.val.det = Real.exp (2 * ∑ j, alpha g j) := by
  have h := norm_detPower_eq_exp_alpha g 1
  have hpos : 0 < complexNormalizedAbs g.val.det := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr g.det_ne_zero)
  simpa only [ArchimedeanLocal.detPower, one_mul, Complex.norm_exp, Complex.ofReal_re,
    Complex.one_re, mul_one, Real.exp_log hpos] using h

theorem exists_exp_alpha_unitary_mul_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k : K) (g : G) (i : Fin n),
      Real.exp (alpha (k.val * g) i) ≤ C * ‖g.val‖ := by
  have hC : Continuous (fun k : K => k.val.val) := Units.continuous_val.comp continuous_subtype_val
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hC.continuousOn
  let C := max 1 B
  have hC₁ : 1 ≤ C := le_max_left _ _
  have hC₀ : 0 ≤ C := zero_le_one.trans hC₁
  have hK (k : K) : ‖k.val.val‖ ≤ C := (hB k (Set.mem_univ k)).trans (le_max_right _ _)
  refine ⟨C ^ 2, one_le_pow₀ hC₁, fun k g i => ?_⟩
  let h := k.val * g
  calc
    Real.exp (alpha h i) = ‖(bpart h).val i i‖ := by
      rw [← exp_alpha, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    _ ≤ ‖(bpart h).val‖ := norm_entry_le_operator _ _ _
    _ ≤ (‖k.val.val‖ * ‖g.val‖) * ‖((kpart h)⁻¹ : K).val.val‖ := by
      change ‖(k.val.val * g.val) * ((kpart h)⁻¹ : K).val.val‖ ≤ _
      exact (Matrix.linfty_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (C * ‖g.val‖) * C :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hK k) (norm_nonneg _))
        (hK ((kpart h)⁻¹)) (norm_nonneg _) (mul_nonneg hC₀ (norm_nonneg _))
    _ = C ^ 2 * ‖g.val‖ := by ring

/-- The determinant norm is the exponential of twice the sum of the logarithms.
The positive diagonal entries of a unitary left translate are bounded uniformly by
the matrix norm. -/
def ComplexLocalIwasawaLogBoundsStatement : Prop :=
  (∀ g : G, complexNormalizedAbs g.val.det = Real.exp (2 * ∑ j, alpha g j)) ∧
  (∃ C : ℝ, 1 ≤ C ∧ ∀ (k : K) (g : G) (i : Fin n),
    Real.exp (alpha (k.val * g) i) ≤ C * ‖g.val‖)

theorem complexLocalIwasawaLogBounds : ComplexLocalIwasawaLogBoundsStatement (n := n) :=
  ⟨complexNormalizedAbs_det_eq_exp_alpha, exists_exp_alpha_unitary_mul_le⟩

end Langlands.Global.RankinSelbergGlobal.ComplexLocalIwasawa
