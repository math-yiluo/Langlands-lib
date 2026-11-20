import Langlands.Global.RankinSelberg.ComplexGodementAdditiveDiagonal
import Langlands.Analysis.SchwartzCompactAverage
import Langlands.Analysis.SchwartzMarginal
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # The Schwartz diagonal test of a complex Godement section -/

noncomputable section

open MeasureTheory Matrix
open scoped SchwartzMap Matrix.Norms.Operator

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance schwartzDiagonalGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance schwartzDiagonalGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance schwartzDiagonalGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "H" => Langlands.GeneralLinear (n + 1) ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Z" => (Fin n → ℂ)
local notation "X" => (UpperEntryPair n → ℂ)
local notation "Square" => Matrix (Fin n) (Fin n) ℂ
local notation "Rect" => Matrix (Fin n) (Fin (n + 1)) ℂ

private def triangularLinear : Z × X →ₗ[ℝ] Square where
  toFun p := upperTriangularEntries p.1 p.2
  map_add' p q := by
    ext i j
    by_cases h : i < j <;> simp [upperTriangularEntries, h]
    split_ifs <;> simp
  map_smul' r p := by
    ext i j
    by_cases h : i < j <;> simp [upperTriangularEntries, h]

private def extractTriangular : Rect →ₗ[ℝ] Z × X where
  toFun M := (fun j => M j j.succ, fun ij => M ij.1.1 ij.1.2.succ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def triangularPullback (g : H) : Square →ₗ[ℝ] (Z × X →L[ℝ] Rect) where
  toFun k := ((mulRightLinearMap (Fin n) ℝ (trailingRows g.val)).comp
    ((mulLeftLinearMap (Fin n) ℝ k).comp triangularLinear)).toContinuousLinearMap
  map_add' k l := by
    apply ContinuousLinearMap.ext
    intro p
    change (k + l) * upperTriangularEntries p.1 p.2 * trailingRows g.val =
      k * upperTriangularEntries p.1 p.2 * trailingRows g.val +
      l * upperTriangularEntries p.1 p.2 * trailingRows g.val
    rw [Matrix.add_mul, Matrix.add_mul]
  map_smul' r k := by
    apply ContinuousLinearMap.ext
    intro p
    change (r • k) * upperTriangularEntries p.1 p.2 * trailingRows g.val =
      r • (k * upperTriangularEntries p.1 p.2 * trailingRows g.val)
    rw [Matrix.smul_mul, Matrix.smul_mul]

private def triangularLeftInverse (g : H) : Square →ₗ[ℝ] (Rect →L[ℝ] Z × X) where
  toFun k := (extractTriangular.comp ((mulLeftLinearMap (Fin (n + 1)) ℝ k).comp
    (mulRightLinearMap (Fin n) ℝ g⁻¹.val))).toContinuousLinearMap
  map_add' k l := by
    apply ContinuousLinearMap.ext
    intro M
    change extractTriangular ((k + l) * (M * g⁻¹.val)) =
      extractTriangular (k * (M * g⁻¹.val)) + extractTriangular (l * (M * g⁻¹.val))
    rw [Matrix.add_mul, map_add]
  map_smul' r k := by
    apply ContinuousLinearMap.ext
    intro M
    change extractTriangular ((r • k) * (M * g⁻¹.val)) = r • extractTriangular (k * (M * g⁻¹.val))
    rw [Matrix.smul_mul, map_smul]

private theorem triangularLeftInverse_apply (g : H) (k : G) (p : Z × X) :
    triangularLeftInverse g k⁻¹.val (triangularPullback g k.val p) = p := by
  let T := upperTriangularEntries p.1 p.2
  have hR : trailingRows g.val * g⁻¹.val = trailingRows 1 := by
    calc
      _ = (g.val * g⁻¹.val).submatrix Fin.succ id :=
        (Matrix.submatrix_mul g.val g⁻¹.val Fin.succ id id Function.bijective_id).symm
      _ = _ := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
  change extractTriangular (k⁻¹.val * (((k.val * T) * trailingRows g.val) * g⁻¹.val)) = p
  rw [Matrix.mul_assoc (k.val * T), hR, ← Matrix.mul_assoc k⁻¹.val (k.val * T),
    ← Matrix.mul_assoc k⁻¹.val k.val, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  have he (i j : Fin n) : (T * trailingRows (m := n) 1) i j.succ = T i j := by
    simp [trailingRows, Matrix.mul_apply, Matrix.one_apply, mul_ite]
  apply Prod.ext
  · funext i
    change (T * trailingRows (m := n) 1) i i.succ = p.1 i
    rw [he]
    simp [T, upperTriangularEntries]
  · funext ij
    change (T * trailingRows (m := n) 1) ij.1.1 ij.1.2.succ = p.2 ij
    rw [he]
    simp [T, upperTriangularEntries, ij.2]

private theorem exists_triangularPullback_lower (g : H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : Z × X) (k : K), ‖p‖ ≤ C * ‖triangularPullback g k.val p‖ := by
  let B (k : K) := triangularLeftInverse g k.val⁻¹.val
  have hB : Continuous B := (triangularLeftInverse g).toContinuousLinearMap.continuous.comp
    (Units.continuous_val.comp continuous_subtype_val.inv)
  obtain ⟨M, hM⟩ := (isCompact_univ.image hB.norm).bddAbove
  refine ⟨max M 0, le_max_right _ _, fun p k => ?_⟩
  calc
    ‖p‖ = ‖B k (triangularPullback g k.val p)‖ := congrArg norm
      (triangularLeftInverse_apply g k.val p).symm
    _ ≤ ‖B k‖ * ‖triangularPullback g k.val p‖ := (B k).le_opNorm _
    _ ≤ max M 0 * ‖triangularPullback g k.val p‖ :=
      mul_le_mul_of_nonneg_right ((hM ⟨k, Set.mem_univ k, rfl⟩).trans (le_max_left _ _)) (norm_nonneg _)

/-- Averaging the complex Godement test over the unitary group and integrating the strictly
upper entries gives a Schwartz function of the additive diagonal. -/
def ComplexGodementSchwartzDiagonalStatement : Prop :=
  ∀ (κ : Measure K) [IsFiniteMeasure κ] (d : ComplexCharacterData)
    (Φ : 𝓢(Rect, ℂ)) (f : G → ℂ), Continuous f → ∀ g : H,
      ∃ Ψ : 𝓢(Z, ℂ), ∀ a : Z,
        Ψ a = ∫ z : X, ∫ k, diagonalTestKernel d Φ f g a k z ∂κ

theorem complexGodementSchwartzDiagonal : ComplexGodementSchwartzDiagonalStatement (n := n) := by
  intro κ hκ d Φ f hf g
  have : BorelSpace K := inferInstanceAs (BorelSpace (K : Set G))
  let A (k : K) := triangularPullback g k.val
  let w (k : K) := f k.val⁻¹ * (d.character (determinant k.val) : ℂ)
  have hA : Continuous A := (triangularPullback g).toContinuousLinearMap.continuous.comp
    (Units.continuous_val.comp continuous_subtype_val)
  have hw : Continuous w := (hf.comp continuous_subtype_val.inv).mul
    ((Units.continuous_val.comp d.character.continuous).comp
      (determinantContinuous.continuous.comp continuous_subtype_val))
  obtain ⟨C, hC, hLower⟩ := exists_triangularPullback_lower g
  let Ξ := Langlands.Analysis.SchwartzCompactAverage.average w A Φ κ hw hA hC hLower
  refine ⟨Langlands.Analysis.SchwartzMarginal.marginalCLM (volume : Measure X) Ξ, fun a => ?_⟩
  rw [Langlands.Analysis.SchwartzMarginal.marginalCLM_apply]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [show Ξ = Langlands.Analysis.SchwartzCompactAverage.average w A Φ κ hw hA hC hLower from rfl,
    Langlands.Analysis.SchwartzCompactAverage.average_apply]
  apply integral_congr_ae
  filter_upwards [] with k
  change w k * Φ (k.val.val * upperTriangularEntries a z * trailingRows g.val) =
    Φ (k.val.val * upperTriangularEntries a z * trailingRows g.val) * w k
  exact mul_comm _ _

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
