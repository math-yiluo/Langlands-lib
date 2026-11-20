import Langlands.Analysis.SchwartzLinearAverage
import Langlands.Representation.GodementJacquet.ComplexTriangularMatchedTests

/-! # Compact averaging of matrix Schwartz tests and their transforms -/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Analysis Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis

variable {n : ℕ}
local notation "I" => Fin n
local notation "M" => Matrix I I ℂ
local notation "G" => GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n

local instance compactAverageGLMeasurable (m : ℕ) : MeasurableSpace (GeneralLinear m ℂ) := borel _
local instance compactAverageGLBorel (m : ℕ) : BorelSpace (GeneralLinear m ℂ) := ⟨rfl⟩
local instance compactAverageGLSecondCountable (m : ℕ) : SecondCountableTopology (GeneralLinear m ℂ) :=
  (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m).isInducing.secondCountableTopology
local instance compactAverageUnitarySecondCountable (m : ℕ) :
    SecondCountableTopology (unitaryCompact ℂ m) :=
  IsInducing.subtypeVal.secondCountableTopology

local instance compactAverageMatrixSecondCountable : SecondCountableTopology M :=
  inferInstanceAs (SecondCountableTopology (I → I → ℂ))

local instance compactAverageMatrixBorel : BorelSpace M :=
  inferInstanceAs (BorelSpace (I → I → ℂ))

private def rightMatrixMultiplication : M →L[ℝ] M →L[ℝ] M :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      (LinearMap.mk₂ ℝ (fun Y X : M => X * Y)
        (fun Y Z X => Matrix.mul_add X Y Z) (fun c Y X => Matrix.mul_smul X c Y)
        (fun Y X Z => Matrix.add_mul X Z Y) (fun c Y X => Matrix.smul_mul c X Y)))

private def unitaryRightMultiplication (k : Kc) : M →L[ℝ] M :=
  rightMatrixMultiplication k.val.val

private theorem continuous_unitaryRightMultiplication : Continuous (unitaryRightMultiplication (n := n)) :=
  rightMatrixMultiplication.continuous.comp (Units.continuous_val.comp continuous_subtype_val)

private theorem exists_unitaryRightMultiplication_bound :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ k : Kc, ‖unitaryRightMultiplication k‖ ≤ B) ∧
      ∀ (k : Kc) (X : M), ‖X‖ ≤ B * ‖unitaryRightMultiplication k X‖ := by
  let : CompactSpace Kc := ComplexDuality.compactSpace_unitaryCompact n
  obtain ⟨B, hB⟩ := (isCompact_range (continuous_unitaryRightMultiplication (n := n)).norm).bddAbove
  have hB' (k : Kc) : ‖unitaryRightMultiplication k‖ ≤ B := hB (mem_range_self k)
  refine ⟨B, (norm_nonneg _).trans (hB' 1), hB', fun k X => ?_⟩
  have hI : unitaryRightMultiplication k⁻¹ (unitaryRightMultiplication k X) = X := by
    change (X * k.val.val) * (k.val⁻¹).val = X
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have h := (unitaryRightMultiplication k⁻¹).le_opNorm (unitaryRightMultiplication k X)
  rw [hI] at h
  exact h.trans (mul_le_mul_of_nonneg_right (hB' k⁻¹) (norm_nonneg _))

/-- Average a matrix Schwartz test using a weight on the unitary group. -/
def complexMatrixCompactAverage (μK : Measure Kc) (κ : Kc → ℂ) (hκ : Integrable κ μK)
    (Φ : SchwartzMap M ℂ) : SchwartzMap M ℂ :=
  let B := exists_unitaryRightMultiplication_bound (n := n)
  schwartzLinearAverage μK κ hκ unitaryRightMultiplication continuous_unitaryRightMultiplication
    B.choose_spec.2.1 B.choose_spec.1 B.choose_spec.2.2 Φ

theorem complexMatrixCompactAverage_apply (μK : Measure Kc) (κ : Kc → ℂ)
    (hκ : Integrable κ μK) (Φ : SchwartzMap M ℂ) (X : M) :
    complexMatrixCompactAverage μK κ hκ Φ X = ∫ k, κ k * Φ (X * k.val.val) ∂μK := rfl

/-- The Fourier transform of a unitary average is the average of the
transforms with inverse-transpose right translations. -/
theorem complexMatrixFourier_compactAverage (a : ℂˣ) (μK : Measure Kc) [SFinite μK]
    (κ : Kc → ℂ) (hκ : Integrable κ μK) (hκc : Continuous κ)
    (Φ : SchwartzMap M ℂ) (X : M) :
    complexMatrixFourier a (complexMatrixCompactAverage μK κ hκ Φ) X =
      ∫ k, κ k * complexMatrixFourier a Φ (X * (inverseTranspose n ℂ k.val).val) ∂μK := by
  let μ := complexMatrixAddMeasure n a
  let A (Y : M) := traceCharacter a (rectangularPairing Y X)
  let F (k : Kc) (Y : M) := κ k * Φ (Y * k.val.val) * A Y
  have hA : Continuous A := (continuous_traceCharacter a).comp (by
    unfold rectangularPairing
    fun_prop)
  have hF : Continuous (Function.uncurry F) :=
    ((hκc.comp continuous_fst).mul (Φ.continuous.comp (continuous_snd.matrix_mul
      (Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst))))).mul
      (hA.comp continuous_snd)
  have hΦ : Integrable Φ μ := Φ.integrable
  have hFn (k : Kc) (Y : M) : ‖F k Y‖ = ‖κ k‖ * ‖Φ (Y * k.val.val)‖ := by
    simp [F, A]
  have hI : Integrable (Function.uncurry F) (μK.prod μ) := by
    rw [integrable_prod_iff hF.aestronglyMeasurable]
    constructor
    · exact Eventually.of_forall fun k =>
        (((measurePreserving_complexMatrixRightMul_unitary a k).integrable_comp_of_integrable
          hΦ).norm.const_mul ‖κ k‖).mono'
          ((hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
          (Eventually.of_forall fun Y => (hFn k Y).le)
    · refine (hκ.norm.mul_const (∫ Y, ‖Φ Y‖ ∂μ)).congr (Eventually.of_forall fun k => ?_)
      simp_rw [Function.uncurry, hFn]
      have heq : (rectangularLeftRightHomeomorph (1 : G) k.val : M → M) =
          fun Y => Y * k.val.val := by funext Y; simp
      have he : MeasurableEmbedding (fun Y : M => Y * k.val.val) := by
        rw [← heq]
        exact (rectangularLeftRightHomeomorph (1 : G) k.val).measurableEmbedding
      rw [integral_const_mul]
      exact congrArg (‖κ k‖ * ·)
        ((measurePreserving_complexMatrixRightMul_unitary a k).integral_comp he
          (fun Y => ‖Φ Y‖)).symm
  calc
    _ = ∫ Y, (∫ k, F k Y ∂μK) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun Y => by
        change complexMatrixCompactAverage μK κ hκ Φ Y * A Y = _
        rw [complexMatrixCompactAverage_apply, ← integral_mul_const]
    _ = ∫ k, (∫ Y, F k Y ∂μ) ∂μK := (integral_integral_swap hI).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun k => by
        change (∫ Y, F k Y ∂μ) = κ k *
          complexMatrixFourier a Φ (X * (inverseTranspose n ℂ k.val).val)
        rw [← complexMatrixFourier_translate a Φ k X]
        change (∫ Y, κ k * Φ (Y * k.val.val) * A Y ∂μ) =
          κ k * ∫ Y, complexMatrixTranslate k Φ Y * A Y ∂μ
        simp only [complexMatrixTranslate_apply, mul_assoc, integral_const_mul]

end Langlands.GodementJacquet
