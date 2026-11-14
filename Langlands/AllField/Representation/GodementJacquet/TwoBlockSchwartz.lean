import Langlands.Representation.GodementJacquet.TwoBlockSchwartz
import Langlands.AllField.Representation.GodementJacquet.TwoBlockParabolicHaar
/-!
# Upper-block integrals of full-matrix test functions

For a Schwartz–Bruhat function `Φ` on `(t + 1) × (t + 1)` matrices, the upper-block
integral `Φ^P (A, D) = ∫ B, Φ [[A, B], [0, D]] dB` is Schwartz–Bruhat on
`Mat_{n₀} × Mat_{n₁}` and a finite sum of products. The integral of
`Φ (parabolicPoint z) * U z.1` over the parabolic parameters reduces to a Levi
integral of `Φ^P` with the radical factor `|det a|^(-n₁)`.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace Langlands.AllField.GodementJacquet.TwoBlock
open Langlands.GodementJacquet.TwoBlock hiding glSecondCountable instBorelSpaceCarrier instBorelSpaceCarrier_1 instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceCarrier_1 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 integrable_mul_left_radical_iff integral_mul_left_radical integral_testFunction_parabolicPoint map_mul_left_radical matrixLocallyCompact matrixSecondCountable measurableEmbedding_mul_left_radical measurable_parabolicPoint measurePreserving_parabolicShift parabolicMeasure parabolicMeasure_isFiniteMeasureOnCompacts parabolicMeasure_isOpenPosMeasure parabolicMeasure_preimage_ne_top parabolicMeasure_preimage_ne_zero parabolicMeasure_sigmaFinite parabolicPoint_translation radicalWeight
open Langlands.AllField.GodementJacquet.TwoBlock
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet

open Langlands.GeneralLinear
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uR

section Blocks



end Blocks

section Schwartz



end Schwartz

section PiTwo


end PiTwo

section ParabolicIntegral

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance : MeasurableSpace F := borel _
local instance : BorelSpace F := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩

attribute [local instance] glSecondCountable matrixLocallyCompact matrixSecondCountable
  glLocallyCompact

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  (dx : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [dx.IsAddHaarMeasure]

/-- The radical factor `|det a|^(-n₁)` of a Levi element `L = (a, d)`. -/
def radicalWeight (L : (succBlockShape m h).Levi F) : ℂ :=
  ((((((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1) (L 0) : ℝ≥0) : ℝ) ^
    (m 1 + 1))⁻¹ : ℝ) : ℂ)

/-- **Parabolic reduction of a full-matrix test function.** If, for every
Schwartz–Bruhat `α` on `Mat_{n₀} × Mat_{n₁}`, the Levi function
`L ↦ α (a, d) * (U L * |det a|^(-n₁))` is integrable, then
`z ↦ Φ (parabolicPoint z) * U z.1` is integrable for the parabolic measure and its
integral is the Levi integral of `Φ^P (a, d) * U L * |det a|^(-n₁)`. -/
theorem integral_testFunction_parabolicPoint
    (Φ : SchwartzBruhat (Matrix (Fin (t + 1)) (Fin (t + 1)) F))
    (U : (succBlockShape m h).Levi F → ℂ)
    (hU : AEStronglyMeasurable U (Measure.pi fun i : Fin 2 => generalLinearHaar F (m i)))
    (hint : ∀ α : SchwartzBruhat (Matrix (Fin (m 0 + 1)) (Fin (m 0 + 1)) F ×
        Matrix (Fin (m 1 + 1)) (Fin (m 1 + 1)) F),
      Integrable (fun L : (succBlockShape m h).Levi F =>
          α ((L 0).val, (L 1).val) * (U L * radicalWeight F h L))
        (Measure.pi fun i : Fin 2 => generalLinearHaar F (m i))) :
    Integrable (fun z => Φ (parabolicPoint h z).val * U z.1) (parabolicMeasure F h dx) ∧
      ∫ z, Φ (parabolicPoint h z).val * U z.1 ∂(parabolicMeasure F h dx) =
        ∫ L, upperBlockIntegral h Φ dx ((L 0).val, (L 1).val) * (U L * radicalWeight F h L)
          ∂(Measure.pi fun i : Fin 2 => generalLinearHaar F (m i)) := by
  set μL := Measure.pi fun i : Fin 2 => generalLinearHaar F (m i) with hμL
  obtain ⟨N, α, β, hf⟩ := SchwartzBruhat.exists_tensor_expansion (upperBlockRestriction h Φ)
  -- the integrand as a finite sum
  let T : Fin N → (succBlockShape m h).Levi F ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F → ℂ :=
    fun j z => (α j ((z.1 0).val, (z.1 1).val) * U z.1) * β j ((z.1 0).val * z.2)
  have hsum : (fun z => Φ (parabolicPoint h z).val * U z.1) = fun z => ∑ j, T j z := by
    funext z
    obtain ⟨L, x⟩ := z
    have hΦ : Φ (parabolicPoint h (L, x)).val =
        ∑ j, α j ((L 0).val, (L 1).val) * β j ((L 0).val * x) := by
      rw [parabolicPoint_val_eq_upperBlockMap]
      exact hf ((L 0).val, (L 1).val) ((L 0).val * x)
    rw [hΦ, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp only [T]
    ring
  have hcont_x : Continuous fun z : (succBlockShape m h).Levi F ×
      Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F => (z.1 0).val * z.2 :=
    (Units.continuous_val.comp ((continuous_apply (0 : Fin 2)).comp continuous_fst)).matrix_mul
      continuous_snd
  have hcont_L : Continuous fun L : (succBlockShape m h).Levi F =>
      ((L 0).val, (L 1).val) :=
    (Units.continuous_val.comp (continuous_apply (0 : Fin 2))).prodMk
      (Units.continuous_val.comp (continuous_apply (1 : Fin 2)))
  have hradw (L : (succBlockShape m h).Levi F) :
      ‖radicalWeight F h L‖ =
        ((((⟨⟩ : LocalFieldData F).determinantNorm (m 0 + 1) (L 0) : ℝ≥0) : ℝ) ^
          (m 1 + 1))⁻¹ := by
    rw [radicalWeight, Complex.norm_real, Real.norm_of_nonneg]
    positivity
  have hTint (j : Fin N) : Integrable (T j) (parabolicMeasure F h dx) := by
    have hm : AEStronglyMeasurable (T j) (parabolicMeasure F h dx) :=
      ((((α j).continuous.comp hcont_L).aestronglyMeasurable.mul hU).comp_fst).mul
        ((β j).continuous.comp hcont_x).aestronglyMeasurable
    rw [parabolicMeasure, integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall fun L => ?_, ?_⟩
    · show Integrable (fun y => (α j ((L 0).val, (L 1).val) * U L) * β j ((L 0).val * y)) dx
      exact ((integrable_mul_left_radical_iff F dx (L 0) (β j)).mpr
        ((β j).integrable dx)).const_mul _
    · have he : (fun L : (succBlockShape m h).Levi F =>
          ∫ x, ‖T j (L, x)‖ ∂dx) = fun L =>
            ‖α j ((L 0).val, (L 1).val) * (U L * radicalWeight F h L)‖ *
              ∫ y, ‖β j y‖ ∂dx := by
        funext L
        simp only [T, norm_mul]
        rw [integral_const_mul, integral_mul_left_radical F dx (L 0) (fun y => ‖β j y‖),
          hradw, smul_eq_mul]
        ring
      rw [he]
      exact (hint (α j)).norm.mul_const _
  have hTval (j : Fin N) : ∫ z, T j z ∂(parabolicMeasure F h dx) =
      ∫ L, α j ((L 0).val, (L 1).val) * (U L * radicalWeight F h L) * ∫ y, β j y ∂dx ∂μL := by
    rw [parabolicMeasure, integral_prod _ (hTint j)]
    apply integral_congr_ae
    filter_upwards with L
    simp only [T]
    rw [integral_const_mul, integral_mul_left_radical F dx (L 0) (β j), radicalWeight,
      Complex.real_smul]
    push_cast
    ring
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact integrable_finsetSum _ fun j _ => hTint j
  · rw [hsum, integral_finsetSum _ fun j _ => hTint j]
    simp only [hTval]
    rw [← integral_finsetSum _ fun j _ => (hint (α j)).mul_const _]
    apply integral_congr_ae
    filter_upwards with L
    rw [upperBlockIntegral_apply]
    have hB : ∀ B, Φ (Matrix.reindex (blockEquiv h) (blockEquiv h)
        (Matrix.fromBlocks (L 0).val B 0 (L 1).val)) =
          ∑ j, α j ((L 0).val, (L 1).val) * β j B := fun B =>
      (upperBlockRestriction_apply h Φ (L 0).val (L 1).val B).symm.trans (hf _ B)
    simp only [hB]
    rw [integral_finsetSum _ fun j _ => ((β j).integrable dx).const_mul _, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_const_mul]
    ring

end ParabolicIntegral

end Langlands.AllField.GodementJacquet.TwoBlock
