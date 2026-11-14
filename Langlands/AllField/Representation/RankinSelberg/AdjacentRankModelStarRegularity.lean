import Langlands.Representation.RankinSelberg.AdjacentRankModelStarRegularity
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelStarIntegrability
/-! Continuous compactly supported scalar evaluations of whole test tensors. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankModelStarSourceFunction_regularity adjacentRankModelStarTargetFunction_regularity adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs modelStarRegularityLocalField modelStarRegularityTopology modelStarRegularityValuative normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory TensorProduct
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear

universe uF uV

section Evaluation


end Evaluation

section CanonicalTopology

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (r : ℕ)
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
  (s : ℂ)

include hσ

/-- Every original weighted tensor evaluation is continuous with compact
support. No topology on the coefficient module is used. -/
theorem adjacentRankModelStarSourceFunction_regularity
    (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    Continuous (adjacentRankModelStarSourceFunction ψ σ ℓ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ s Ψ) ∧
    HasCompactSupport (adjacentRankModelStarSourceFunction ψ σ ℓ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ s Ψ) := by
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    constructor
    · have hχ : Continuous (fun h : GeneralLinear (r + 1) F =>
          (χ (determinant h) : ℂ)) :=
        Units.continuous_val.comp (χ.continuous.comp determinantContinuous.continuous)
      exact ((((SchwartzBruhat.continuous Φ).comp
        (continuous_adjacentRankKernelMatrix F r)).mul
          ((glModelFunction_continuous ψ r σ hσ ℓ W).comp continuous_inv)).mul hχ).mul
            (continuous_adjacentRank_determinantWeight F _ _)
    · exact ((adjacentRankPure_hasCompactSupport F ψ r σ hσ ℓ Φ W).mul_right).mul_right
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    rw [adjacentRankModelStarSourceFunction_add]
    exact ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

/-- Every weighted tensor evaluation at the transformed coefficient argument
is continuous with compact support, in the original tensor space. -/
theorem adjacentRankModelStarTargetFunction_regularity
    (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    Continuous (adjacentRankModelStarTargetFunction ψ σ ℓ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ s Ψ) ∧
    HasCompactSupport (adjacentRankModelStarTargetFunction ψ σ ℓ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) χ s Ψ) := by
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    constructor
    · have hχ : Continuous (fun h : GeneralLinear (r + 1) F =>
          (χ⁻¹ (determinant h) : ℂ)) :=
        Units.continuous_val.comp ((χ⁻¹).continuous.comp determinantContinuous.continuous)
      have harg : Continuous (fun h : GeneralLinear (r + 1) F =>
          weylLong (r + 1) F * inverseTranspose (r + 1) F h⁻¹) :=
        continuous_const.mul ((continuous_inverseTranspose _ _).comp continuous_inv)
      exact ((((SchwartzBruhat.continuous Φ).comp
        (continuous_adjacentRankKernelMatrix F r)).mul
          ((glModelFunction_continuous ψ r σ hσ ℓ W).comp harg)).mul hχ).mul
            (continuous_adjacentRank_determinantWeight F _ _)
    · exact ((adjacentRankTransformedPure_hasCompactSupport F ψ r σ hσ ℓ Φ W).mul_right).mul_right
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    rw [adjacentRankModelStarTargetFunction_add]
    exact ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

end CanonicalTopology

end Langlands.AllField.RankinSelberg
