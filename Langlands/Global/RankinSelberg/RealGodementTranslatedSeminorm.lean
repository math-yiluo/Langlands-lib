import Langlands.Analysis.SchwartzLinearAverage
import Langlands.Global.RankinSelberg.RealGodementFourierCovariance
import Langlands.Global.RankinSelberg.RealMatrixHeightBounds

/-! # Polynomial Schwartz seminorm bounds under real rectangular right translation -/

noncomputable section

open Langlands.GeneralLinear
open scoped ContDiff Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealPlaceRestriction

variable {m n : ℕ}

local notation "H" => Langlands.GeneralLinear n ℝ
local notation "X" => Matrix (Fin m) (Fin n) ℝ

private def rightMulLinear (g : H) : X →L[ℝ] X :=
  ({ toFun := fun x => x * g.val
     map_add' := fun x y => Matrix.add_mul x y g.val
     map_smul' := fun c x => Matrix.smul_mul c x g.val } : X →ₗ[ℝ] X).toContinuousLinearMap

private theorem linfty_opNorm_le_height (hn : 0 < n) (g : H) :
    ‖g.val‖ ≤ (n : ℝ) * realMatrixHeight g := by
  let R : ℝ≥0 := ⟨(n : ℝ) * realMatrixHeight g, mul_nonneg (Nat.cast_nonneg _) (realMatrixHeight_nonneg _)⟩
  change ‖g.val‖ ≤ (R : ℝ)
  rw [Matrix.linfty_opNorm_def, NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ => ?_
  apply NNReal.coe_le_coe.mp
  change ((∑ j : Fin n, ‖g.val i j‖₊ : ℝ≥0) : ℝ) ≤ (n : ℝ) * realMatrixHeight g
  rw [NNReal.coe_sum]
  calc
    _ ≤ ∑ _ : Fin n, realMatrixHeight g :=
      Finset.sum_le_sum fun j _ => norm_entry_le_realMatrixHeight hn g i j
    _ = _ := by simp [nsmul_eq_mul]

/-- A defining Schwartz seminorm of the pullback is controlled by one power of the group height. -/
theorem seminorm_rectangularTranslate_right_le (hn : 0 < n) (k j : ℕ) (g : H) (Φ : 𝓢(X, ℂ)) :
    SchwartzMap.seminorm ℝ k j (rectangularTranslate 1 g Φ) ≤
      ((n : ℝ) * realMatrixHeight g) ^ (k + j) * SchwartzMap.seminorm ℝ k j Φ := by
  let R := (n : ℝ) * realMatrixHeight g
  have hR : 0 ≤ R := mul_nonneg (Nat.cast_nonneg _) (realMatrixHeight_nonneg g)
  let L := rightMulLinear (m := m) g
  have hL : ‖L‖ ≤ R := by
    apply ContinuousLinearMap.opNorm_le_bound _ hR
    intro x
    change ‖x * g.val‖ ≤ R * ‖x‖
    rw [mul_comm R]
    exact (Matrix.linfty_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_left (linfty_opNorm_le_height hn g) (norm_nonneg _))
  refine SchwartzMap.seminorm_le_bound ℝ k j _ (mul_nonneg (pow_nonneg hR _) (apply_nonneg _ _)) ?_
  intro x
  have hEq : (rectangularTranslate 1 g Φ : X → ℂ) = Φ ∘ L := by
    funext y
    simp only [rectangularTranslate_apply, Units.val_one, Matrix.one_mul]
    rfl
  have hInv : ‖g⁻¹.val‖ ≤ R := by
    simpa only [realMatrixHeight_inv] using linfty_opNorm_le_height hn g⁻¹
  have hBelow : ‖x‖ ≤ R * ‖L x‖ := by
    change ‖x‖ ≤ R * ‖x * g.val‖
    have hCancel : x * g.val * g⁻¹.val = x := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    calc
      _ = ‖x * g.val * g⁻¹.val‖ := congrArg norm hCancel.symm
      _ ≤ ‖x * g.val‖ * ‖g⁻¹.val‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ ‖x * g.val‖ * R := mul_le_mul_of_nonneg_left hInv (norm_nonneg _)
      _ = _ := mul_comm _ _
  rw [hEq]
  simpa only [R, pow_add] using
    Langlands.Analysis.norm_pow_mul_linearPullbackDerivative_le Φ k j x L hL hR hBelow

/-- Every continuous real Schwartz seminorm grows at most polynomially along the right
translates of the rectangular test, with an exponent chosen before the test. -/
def RealGodementTranslatedSeminormStatement : Prop :=
  ∀ (m n : ℕ), 0 < n →
    ∀ (q : Seminorm ℝ 𝓢(Matrix (Fin m) (Fin n) ℝ, ℂ)), Continuous q →
    ∃ (I : Finset (ℕ × ℕ)) (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (g : Langlands.GeneralLinear n ℝ) (Φ : 𝓢(Matrix (Fin m) (Fin n) ℝ, ℂ)),
        q (rectangularTranslate 1 g Φ) ≤ C * realMatrixHeight g ^ N *
          I.sup (schwartzSeminormFamily ℝ (Matrix (Fin m) (Fin n) ℝ) ℂ) Φ

theorem realGodementTranslatedSeminorm : RealGodementTranslatedSeminormStatement := by
  intro m n hn q hq
  let Rect := Matrix (Fin m) (Fin n) ℝ
  let P := schwartzSeminormFamily ℝ Rect ℂ
  obtain ⟨I, C, _, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ Rect ℂ) q hq
  let N := I.sup fun z => z.1 + z.2
  refine ⟨I, N, (C : ℝ) * (n : ℝ) ^ N, by positivity, ?_⟩
  intro g Φ
  let R := (n : ℝ) * realMatrixHeight g
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le
    (Nat.one_le_cast.mpr hn) ((by norm_num : (1 : ℝ) ≤ 2).trans (two_le_realMatrixHeight hn g))
  have hBound : I.sup P (rectangularTranslate 1 g Φ) ≤ R ^ N * I.sup P Φ := by
    refine Seminorm.finset_sup_apply_le (mul_nonneg (pow_nonneg (zero_le_one.trans hR) _) (apply_nonneg _ _)) ?_
    intro i hi
    refine (seminorm_rectangularTranslate_right_le hn i.1 i.2 g Φ).trans ?_
    exact mul_le_mul (pow_le_pow_right₀ hR (Finset.le_sup (f := fun i => i.1 + i.2) hi))
      (Seminorm.le_finset_sup_apply (p := P) (x := Φ) hi) (apply_nonneg _ _)
      (pow_nonneg (zero_le_one.trans hR) _)
  calc
    _ ≤ (C : ℝ) * I.sup P (rectangularTranslate 1 g Φ) := hC _
    _ ≤ (C : ℝ) * (R ^ N * I.sup P Φ) := mul_le_mul_of_nonneg_left hBound C.coe_nonneg
    _ = _ := by dsimp only [R]; rw [mul_pow]; ring

end Langlands.Global.RankinSelbergGlobal.RealGodement
