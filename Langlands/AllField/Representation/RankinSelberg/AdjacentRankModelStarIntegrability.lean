import Langlands.Representation.RankinSelberg.AdjacentRankModelStarIntegrability
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelStarStatement
/-! Compact support and integrability for the expanded transformed coefficient
in the fixed-Fourier-action adjacent-rank model-star formula. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelStarStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelStarIntegrabilityLocalInstance1 adjacentRankModelStarIntegrabilityLocalInstance2 adjacentRankModelStarIntegrabilityLocalInstance3 adjacentRankModelStarIntegrabilityLocalInstance4 adjacentRankModelStarIntegrabilityLocalInstance5 adjacentRankModelStarIntegrabilityLocalInstance6 adjacentRankModelStarIntegrabilityLocalInstance7 adjacentRankModelStarIntegrabilityLocalInstance8 adjacentRankModelStarIntegrabilityLocalInstance9 adjacentRankPure_hasCompactSupport adjacentRankTransformedIntegrand adjacentRankTransformedPure_hasCompactSupport adjacentRankTransformed_integrable_of_isSmooth continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory TensorProduct
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance adjacentRankModelStarIntegrabilityLocalInstance4 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Compact support for the actual Weyl/inverse-transpose coefficient, without
changing any Fourier action or imposing a topology on the carrier. -/
theorem adjacentRankTransformedPure_hasCompactSupport
    (ψ : UnitaryAdditiveCharacter F) (r : ℕ)
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    HasCompactSupport (fun h : GeneralLinear (r + 1) F =>
      Φ (adjacentRankKernelMatrix h) *
        glModelFunction ψ r σ ℓ W
          (weylLong (r + 1) F * inverseTranspose (r + 1) F h⁻¹)) := by
  obtain ⟨v, hv⟩ := W.property
  let ℓ' : glFunctionals (ψ.scale (-1)) r (inverseTransposePullback σ) :=
    ⟨(dualFunctional ψ σ ℓ).val, by
      simpa only [glFunctionals, glInverseFunctionals, standardCharacter_scale_neg_one] using
        (dualFunctional ψ σ ℓ).property⟩
  have he (a : GeneralLinear (r + 1) F) :
      glModelFunction ψ r σ ℓ W
          (weylLong (r + 1) F * inverseTranspose (r + 1) F a) =
        glModelFunction (ψ.scale (-1)) r (inverseTransposePullback σ) ℓ'
          (modelMap (inverseTransposePullback σ) ℓ' v) a := by
    change W.val.val _ = _
    rw [← hv]
    change ℓ.val (σ (weylLong (r + 1) F *
      inverseTranspose (r + 1) F a) v) =
        ℓ.val (σ (weylLong (r + 1) F)
          (σ (inverseTranspose (r + 1) F a) v))
    rw [map_mul, Module.End.mul_apply]
  simpa only [he] using
    adjacentRankPure_hasCompactSupport F (ψ.scale (-1)) r
      (inverseTransposePullback σ) (inverseTransposePullback_isSmooth σ hσ)
      ℓ' Φ (modelMap (inverseTransposePullback σ) ℓ' v)

local instance adjacentRankModelStarIntegrabilityLocalInstance5 : MeasurableSpace F := borel _
local instance adjacentRankModelStarIntegrabilityLocalInstance6 : BorelSpace F := ⟨rfl⟩
local instance adjacentRankModelStarIntegrabilityLocalInstance7 : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance adjacentRankModelStarIntegrabilityLocalInstance8 (r : ℕ) : MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance adjacentRankModelStarIntegrabilityLocalInstance9 (r : ℕ) : BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩

/-- The fixed-action integrand with its transformed coefficient argument
expanded. The input tensor may already have had its Schwartz factor Fourier
transformed; this definition performs no coefficient-space identification. -/
def adjacentRankTransformedIntegrand
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ ν) {r : ℕ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) (k : GeneralLinear (r + 2) F)
    (h : GeneralLinear (r + 1) F) : ℂ :=
  adjacentRankTestEvaluation ψ σ ℓ (adjacentRankRho0 ψ ν hself σ ℓ k Ψ)
    (adjacentRankKernelMatrix h)
    (weylLong (r + 1) F * inverseTranspose (r + 1) F h⁻¹) *
    (χ⁻¹ (determinant h) : ℂ) *
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) h ((r : ℂ) / 2)

/-- Every test tensor has an integrable expanded transformed-coefficient
integrand, with the Fourier action still at the supplied character `ψ`. -/
theorem adjacentRankTransformed_integrable_of_isSmooth
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ ν) (r : ℕ)
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) (k : GeneralLinear (r + 2) F) :
    Integrable (adjacentRankTransformedIntegrand F ψ ν hself σ ℓ χ Ψ k)
      (generalLinearHaar F r) := by
  unfold adjacentRankTransformedIntegrand
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    let Φ' := rectangularRho0 ψ ν (r + 1) hself k Φ
    change Integrable (fun h : GeneralLinear (r + 1) F =>
      Φ' (adjacentRankKernelMatrix h) *
        glModelFunction ψ r σ ℓ W
          (weylLong (r + 1) F * inverseTranspose (r + 1) F h⁻¹) *
        (χ⁻¹ (determinant h) : ℂ) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) h ((r : ℂ) / 2))
      (generalLinearHaar F r)
    apply Continuous.integrable_of_hasCompactSupport
    · have hχ : Continuous fun h : GeneralLinear (r + 1) F =>
          (χ⁻¹ (determinant h) : ℂ) :=
        Units.continuous_val.comp ((χ⁻¹).continuous.comp determinantContinuous.continuous)
      have harg : Continuous fun h : GeneralLinear (r + 1) F =>
          weylLong (r + 1) F * inverseTranspose (r + 1) F h⁻¹ :=
        continuous_const.mul ((continuous_inverseTranspose _ _).comp continuous_inv)
      exact ((((SchwartzBruhat.continuous Φ').comp
        (continuous_adjacentRankKernelMatrix F r)).mul
          ((glModelFunction_continuous ψ r σ hσ ℓ W).comp harg)).mul hχ).mul
            (continuous_adjacentRank_determinantWeight F _ _)
    · exact ((adjacentRankTransformedPure_hasCompactSupport F ψ r σ hσ ℓ Φ' W).mul_right).mul_right
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    have he : (fun h : GeneralLinear (r + 1) F =>
        adjacentRankTestEvaluation ψ σ ℓ
          (adjacentRankRho0 ψ ν hself σ ℓ k (Ψ₁ + Ψ₂))
          (adjacentRankKernelMatrix h)
          (weylLong (r + 1) F * inverseTranspose (r + 1) F h⁻¹) *
          (χ⁻¹ (determinant h) : ℂ) *
          determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) h ((r : ℂ) / 2)) =
        (fun h =>
          adjacentRankTestEvaluation ψ σ ℓ (adjacentRankRho0 ψ ν hself σ ℓ k Ψ₁)
            (adjacentRankKernelMatrix h)
            (weylLong (r + 1) F * inverseTranspose (r + 1) F h⁻¹) *
            (χ⁻¹ (determinant h) : ℂ) *
            determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) h ((r : ℂ) / 2)) +
        (fun h =>
          adjacentRankTestEvaluation ψ σ ℓ (adjacentRankRho0 ψ ν hself σ ℓ k Ψ₂)
            (adjacentRankKernelMatrix h)
            (weylLong (r + 1) F * inverseTranspose (r + 1) F h⁻¹) *
            (χ⁻¹ (determinant h) : ℂ) *
            determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) h ((r : ℂ) / 2)) := by
      funext h
      simp only [map_add, adjacentRankTestEvaluation_add, Pi.add_apply, add_mul]
    rw [he]
    exact h₁.add h₂

end Langlands.AllField.RankinSelberg
