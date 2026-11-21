import Langlands.Global.RankinSelberg.ComplexOppositeCompactChart
import Langlands.Global.RankinSelberg.ComplexOppositeMoment
import Langlands.Representation.GodementJacquet.ComplexMatrixConvergence
import Langlands.Representation.GodementJacquet.ComplexPrincipalSeriesGrowth

/-! # Polynomial growth of the scalar extension factor on the complex opposite cell -/

noncomputable section

open scoped Classical Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexOppositeScalarGrowth

open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent
  principalSeries principalSeriesCharacter)
open Langlands.Archimedean.ComplexGramFormula (phaseUnit norm_phaseUnit)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (det_upperUnipotent)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (extension extension_mem_principalSeries)
open Langlands.Archimedean.GramFormula (shiftedExponent)
open Langlands.GodementJacquet (complexMatrixHeight_mul_det_bound exists_complexPrincipalSeries_height_bound)
open ArchimedeanLocal (complexNormalizedAbs)
open ComplexModulusOpenCell (groupTranspose_val)
open ComplexOppositeCompactChart (Coordinates oppositePoint oppositeScalar extension_oppositePoint)
open ComplexOppositeMoment (norm_upperEntries)

local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "UC" => fun n => Matrix.unitaryGroup (Fin n) ℂ

private def scalarExponent {n : ℕ} (s : Fin n → ℂ) (j : ℕ) : ℂ :=
  if hj : j < n then s ⟨j, hj⟩ - (((n : ℂ) - 1) / 2 - (j : ℂ)) else 0

private def scalarCharacter (e : ℕ → ℂ) (j : ℕ) (a : ℂˣ) : ℂ :=
  ((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e j

private theorem scalarCharacter_eq_character (e : ℕ → ℂ) (j : ℕ) (a : ℂˣ) :
    scalarCharacter e j a = ((characterOfParams 0 (e j)).character a : ℂ) := by
  rw [(characterOfParams 0 (e j)).character_eq]
  simp only [scalarCharacter, characterOfParams_weight, characterOfParams_exponent, zpow_zero, one_mul]
  rw [Complex.ofReal_pow, pow_two, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _),
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr a.ne_zero)), ← two_mul]

private theorem scalarExtension_mem {n : ℕ} (s : Fin n → ℂ) :
    extension s (fun _ : UC n => (1 : ℂ)) ∈ principalSeries ℂ n (scalarCharacter (scalarExponent s)) := by
  let e := scalarExponent s
  have he : shiftedExponent n e = s := by
    funext i
    simp only [e, shiftedExponent, scalarExponent, dite_eq_left i.isLt]
    ring
  have hχ : ∀ (j : ℕ) (a : ℂˣ), scalarCharacter e j a = scalarCharacter e j (phaseUnit a) *
      ((‖(a : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e j := by
    intro j a
    simp [scalarCharacter, norm_phaseUnit]
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun _ : UC n => fun _ : UC n => (1 : ℂ))) := by
    rw [Set.range_const]
    infer_instance
  have hm := extension_mem_principalSeries e hχ continuous_const hfin (fun a k => by
    simp [principalSeriesCharacter, scalarCharacter, norm_phaseUnit])
  rw [he] at hm
  exact hm

private theorem det_oppositePoint {n : ℕ} (z : Coordinates n) : (oppositePoint z).val.det = 1 := by
  rw [oppositePoint, groupTranspose_val, Matrix.det_transpose]
  exact det_upperUnipotent _

private theorem norm_oppositePoint_val {r : ℕ} (z : Coordinates (r + 1)) :
    ‖(oppositePoint z).val‖ ≤ 1 + ‖z‖ := by
  let e := GeneralLinear.upperEntryCoordinates (K := ℂ) (r + 1)
  let u := e.symm z
  have h : ‖u.val.val - 1‖ = ‖z‖ := by
    rw [← norm_upperEntries u]
    exact congrArg norm (e.apply_symm_apply z)
  change ‖(ComplexModulusOpenCell.groupTranspose u.val).val‖ ≤ _
  rw [groupTranspose_val, Matrix.norm_transpose, ← h]
  have h₁ : ‖(1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)‖ ≤ 1 := by
    refine (Matrix.norm_le_iff zero_le_one).mpr fun i j => ?_
    rw [Matrix.one_apply]
    split <;> simp
  calc
    ‖u.val.val‖ = ‖1 + (u.val.val - 1)‖ := congrArg norm (by abel)
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add h₁ le_rfl)

/-- For each fixed parameter, the opposite-cell scalar factor grows at most polynomially
in the exact upper-entry supremum norm. -/
def ComplexOppositeScalarGrowthStatement : Prop :=
  ∀ (r : ℕ) (s : Fin (r + 1) → ℂ), ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
    ∀ z : Coordinates (r + 1), ‖oppositeScalar s z‖ ≤ C * (1 + ‖z‖) ^ M

theorem complexOppositeScalarGrowth : ComplexOppositeScalarGrowthStatement := by
  intro r s
  let n := r + 1
  let f : G n → ℂ := extension s (fun _ : UC n => 1)
  let d := fun i : Fin n => characterOfParams 0 (scalarExponent s i.val)
  obtain ⟨C, N, hC, h⟩ := exists_complexPrincipalSeries_height_bound d _
    (fun i a => scalarCharacter_eq_character (scalarExponent s) i.val a) f (scalarExtension_mem s)
  let B : ℝ := 2 * (n : ℝ) ^ 2 * (Nat.factorial n : ℝ) ^ 2
  let B' := B * (2 : ℝ) ^ (2 * (n + 1))
  refine ⟨C * B' ^ N, 2 * (n + 1) * N, mul_nonneg hC (by dsimp only [B', B]; positivity), fun z => ?_⟩
  have hH₀ := complexMatrixHeight_mul_det_bound (oppositePoint z)
  rw [det_oppositePoint, complexNormalizedAbs, norm_one, one_pow, mul_one] at hH₀
  have hH₁ : complexMatrixHeight (oppositePoint z) ≤ B * (1 + ‖(oppositePoint z).val‖) ^ (2 * (n + 1)) := by
    simpa [B, n] using hH₀
  have hH : complexMatrixHeight (oppositePoint z) ≤ B' * (1 + ‖z‖) ^ (2 * (n + 1)) := by
    have hnorm : 1 + ‖(oppositePoint z).val‖ ≤ 2 * (1 + ‖z‖) := by
      linarith [norm_oppositePoint_val z, norm_nonneg z]
    calc
      _ ≤ B * (1 + ‖(oppositePoint z).val‖) ^ (2 * (n + 1)) := hH₁
      _ ≤ B * (2 * (1 + ‖z‖)) ^ (2 * (n + 1)) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hnorm _) (by dsimp only [B]; positivity)
      _ = _ := by rw [mul_pow, ← mul_assoc]
  have hg : 0 ≤ complexMatrixHeight (oppositePoint z) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have hf : f (oppositePoint z) = oppositeScalar s z := by
    change extension s (fun _ : UC n => 1) (oppositePoint z) = _
    rw [extension_oppositePoint, mul_one]
  rw [← hf]
  calc
    _ ≤ C * complexMatrixHeight (oppositePoint z) ^ N := h _
    _ ≤ C * (B' * (1 + ‖z‖) ^ (2 * (n + 1))) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg hH N) hC
    _ = _ := by rw [mul_pow, ← pow_mul, ← mul_assoc]

end Langlands.Global.RankinSelbergGlobal.ComplexOppositeScalarGrowth
