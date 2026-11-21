import Langlands.Global.RankinSelberg.ComplexCompactDualProbe
import Langlands.Global.RankinSelberg.ComplexOppositeScalarGrowth

/-! # Uniform value and first-order bounds for the complex compact probe -/

noncomputable section

open Matrix Set
open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexCompactProbeBounds

open Langlands.Archimedean.ComplexGramFormula (complexPositionExponent)
open Langlands.Archimedean.GramFormula (shiftedExponent)
open Langlands.Archimedean.UnitaryFinitePolynomial (compactSpace_unitary)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactDualProbe (dualSection probe norm_probe_le norm_probe_sub_le)
open ComplexOppositeCompactChart (Coordinates oppositePoint oppositeScalar oppositeCompact
  extension_oppositePoint complexOppositeCompactChart)
open ComplexOppositeScalarGrowth (complexOppositeScalarGrowth)

local notation "UC" => fun n => Matrix.unitaryGroup (Fin n) ℂ
local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "Std" => Automorphic.complexStandardKFinite

variable {n : ℕ} {ds : List ComplexCharacterData}

/-- A uniform value bound on the restriction of a standard vector to the compact subgroup. -/
def CompactBound (f : Std n ds) (R : ℝ) : Prop :=
  ∀ x : UC n, ‖f.val (Unitary.toUnits x)‖ ≤ R

/-- A bound on all first right-translation differences in the compact picture. -/
def CompactRightDifferenceBound (f : Std n ds) (D : ℝ) : Prop :=
  ∀ x k : UC n, ‖f.val (Unitary.toUnits (x * k)) - f.val (Unitary.toUnits x)‖ ≤ D * ‖k.val - 1‖

private theorem uniform_compact_conjugate_inverse_bound (n : ℕ) :
    ∃ J : ℝ, 1 ≤ J ∧ ∀ y k : UC n, ‖(y⁻¹ * k⁻¹ * y : UC n).val - 1‖ ≤ J * ‖k.val - 1‖ := by
  let : CompactSpace (UC n) := compactSpace_unitary n
  obtain ⟨B, hB⟩ := (isCompact_range (continuous_subtype_val.norm :
    Continuous (fun k : UC n => ‖k.val‖))).bddAbove
  let C := max B 1
  have hC : 1 ≤ C := le_max_right _ _
  have hCn : 0 ≤ C := zero_le_one.trans hC
  have hK (k : UC n) : ‖k.val‖ ≤ C := (hB (mem_range_self k)).trans (le_max_left _ _)
  refine ⟨C * C, one_le_mul_of_one_le_of_one_le hC hC, fun y k => ?_⟩
  have h : (y⁻¹ * k⁻¹ * y : UC n).val - 1 =
      (y⁻¹ * k⁻¹ : UC n).val * (1 - k.val) * y.val := by
    rw [mul_sub, sub_mul, Matrix.mul_one]
    congr 1
    have h₁ : (y⁻¹ * k⁻¹ * k * y : UC n) = 1 := by group
    exact (congrArg Subtype.val h₁).symm
  rw [h]
  calc
    _ ≤ (‖(y⁻¹ * k⁻¹ : UC n).val‖ * ‖1 - k.val‖) * ‖y.val‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (C * ‖1 - k.val‖) * C :=
      mul_le_mul (mul_le_mul_of_nonneg_right (hK _) (norm_nonneg _)) (hK _) (norm_nonneg _)
        (mul_nonneg hCn (norm_nonneg _))
    _ = _ := by rw [norm_sub_rev]; ring

private theorem norm_probe_sub_of_rightDifference (J : ℝ)
    (hJ : ∀ y k : UC n, ‖(y⁻¹ * k⁻¹ * y : UC n).val - 1‖ ≤ J * ‖k.val - 1‖)
    (f : Std n ds) {D : ℝ} (hD : 0 ≤ D) (hd : CompactRightDifferenceBound f D) (x k : UC n) :
    ‖probe f x k - f.val (Unitary.toUnits x)‖ ≤ D * J * ‖k.val - 1‖ := by
  apply norm_probe_sub_le
  intro y
  have h : k⁻¹ * y = y * (y⁻¹ * k⁻¹ * y) := by group
  rw [h, mul_assoc D]
  exact (hd y (y⁻¹ * k⁻¹ * y)).trans (mul_le_mul_of_nonneg_left (hJ y k) hD)

/-- At any fixed inducing data the compact probe is polynomially bounded globally, and its
error from identity evaluation carries one additional factor of the coordinate norm. -/
def ComplexCompactProbeBoundsStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData), ∃ (M : ℕ) (C E : ℝ), 0 ≤ C ∧ 0 ≤ E ∧
    ∀ (f : Std (r + 1) ds) (x : UC (r + 1)) (z : Coordinates (r + 1)) (R D : ℝ),
      0 ≤ D → CompactBound f R →
      ‖dualSection f x (oppositePoint z)‖ ≤ C * R * (1 + ‖z‖) ^ M ∧
      (CompactRightDifferenceBound f D →
        ‖dualSection f x (oppositePoint z) - f.val (Unitary.toUnits x)‖ ≤
          E * (R + D) * ‖z‖ * (1 + ‖z‖) ^ M)

theorem complexCompactProbeBounds : ComplexCompactProbeBoundsStatement := by
  intro r ds
  let n := r + 1
  let s := shiftedExponent n (fun i => -complexPositionExponent ds i)
  obtain ⟨C, M, hC, hGrowth⟩ := complexOppositeScalarGrowth r s
  obtain ⟨ρ, L, hρ, hL, hLocal⟩ := complexOppositeCompactChart n s
  obtain ⟨J, hJ, hConj⟩ := uniform_compact_conjugate_inverse_bound n
  let E₁ := L * J
  let E₂ := (C + 1) * ρ⁻¹
  let E := max E₁ E₂
  have hE₁ : 0 ≤ E₁ := mul_nonneg hL (zero_le_one.trans hJ)
  refine ⟨M, C, E, hC, hE₁.trans (le_max_left _ _), fun f x z R D hD hR => ?_⟩
  have hR₀ : 0 ≤ R := (norm_nonneg _).trans (hR x)
  let P := (1 + ‖z‖) ^ M
  have hP : 1 ≤ P := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))
  have hP₀ : 0 ≤ P := zero_le_one.trans hP
  let σ := oppositeScalar s z
  let k := oppositeCompact z
  let F := probe f x k
  let y := f.val (Unitary.toUnits x)
  have hf : dualSection f x (oppositePoint z) = σ * F := extension_oppositePoint _ _ _
  have hF : ‖F‖ ≤ R := norm_probe_le f x k hR
  have hy : ‖y‖ ≤ R := hR x
  have hValue : ‖dualSection f x (oppositePoint z)‖ ≤ C * R * P := by
    rw [hf, norm_mul]
    calc
      _ ≤ (C * P) * R := mul_le_mul (hGrowth z) hF (norm_nonneg _) (mul_nonneg hC hP₀)
      _ = _ := by ring
  refine ⟨hValue, fun hd => ?_⟩
  have hRD : 0 ≤ R + D := add_nonneg hR₀ hD
  have hmon {A : ℝ} (hA : A ≤ E) : A * (R + D) * ‖z‖ * P ≤ E * (R + D) * ‖z‖ * P :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hRD)
      (norm_nonneg _)) hP₀
  by_cases hz : ‖z‖ < ρ
  · obtain ⟨hσ, hk⟩ := hLocal z hz
    have hDiff := norm_probe_sub_of_rightDifference J hConj f hD hd x k
    change ‖dualSection f x (oppositePoint z) - y‖ ≤ _
    rw [hf, show σ * F - y = (σ - 1) * F + (F - y) by ring]
    calc
      _ ≤ ‖σ - 1‖ * ‖F‖ + ‖F - y‖ := (norm_add_le _ _).trans_eq (by rw [norm_mul])
      _ ≤ (L * ‖z‖) * R + (D * J) * (L * ‖z‖) :=
        add_le_add (mul_le_mul hσ hF (norm_nonneg _) (mul_nonneg hL (norm_nonneg _)))
          (hDiff.trans (mul_le_mul_of_nonneg_left hk (mul_nonneg hD (zero_le_one.trans hJ))))
      _ = L * (R + D * J) * ‖z‖ := by ring
      _ ≤ L * (J * (R + D)) * ‖z‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        apply mul_le_mul_of_nonneg_left _ hL
        have hJR := mul_le_mul_of_nonneg_right hJ hR₀
        linarith
      _ = E₁ * (R + D) * ‖z‖ := by dsimp only [E₁]; ring
      _ ≤ E₁ * (R + D) * ‖z‖ * P :=
        le_mul_of_one_le_right (mul_nonneg (mul_nonneg hE₁ hRD) (norm_nonneg _)) hP
      _ ≤ _ := hmon (le_max_left _ _)
  · have hFar : 1 ≤ ρ⁻¹ * ‖z‖ := by
      rw [← inv_mul_cancel₀ hρ.ne']
      exact mul_le_mul_of_nonneg_left (le_of_not_gt hz) (inv_nonneg.mpr hρ.le)
    calc
      _ ≤ ‖dualSection f x (oppositePoint z)‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ C * R * P + R := add_le_add hValue hy
      _ ≤ C * R * P + R * P := add_le_add le_rfl (le_mul_of_one_le_right hR₀ hP)
      _ = ((C + 1) * R) * P := by ring
      _ ≤ (((C + 1) * (R + D)) * (ρ⁻¹ * ‖z‖)) * P := by
        apply mul_le_mul_of_nonneg_right _ hP₀
        calc
          _ ≤ (C + 1) * (R + D) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hD) (by positivity)
          _ ≤ _ := le_mul_of_one_le_right (mul_nonneg (by positivity) hRD) hFar
      _ = E₂ * (R + D) * ‖z‖ * P := by dsimp only [E₂]; ring
      _ ≤ _ := hmon (le_max_right _ _)

end Langlands.Global.RankinSelbergGlobal.ComplexCompactProbeBounds
