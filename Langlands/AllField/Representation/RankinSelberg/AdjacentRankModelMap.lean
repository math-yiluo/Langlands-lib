import Langlands.Representation.RankinSelberg.AdjacentRankModelMap
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
/-!
# The linear adjacent-rank integral map

The literal integral on the whole algebraic tensor product is a linear map.
Its image is the span of the pure-tensor integrals. The partial Fourier
equivalence acts on this whole tensor product, and its conjugacy relation
is compatible with the literal integral.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory TensorProduct
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker

universe uF uV

section Fourier


end Fourier

namespace Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges adjacentRankModelConverges_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegral_mul adjacentRankModelMap adjacentRankModelMapBorel adjacentRankModelMapDisconnected adjacentRankModelMapGLMeasurable adjacentRankModelMapLocalField adjacentRankModelMapMeasurable adjacentRankModelMapT2 adjacentRankModelMapTopology adjacentRankModelMapValuative adjacentRankModelMap_apply instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelConverges EqualRankAnalyticStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance adjacentRankModelMapT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance adjacentRankModelMapDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance adjacentRankModelMapMeasurable : MeasurableSpace F := borel _
local instance adjacentRankModelMapBorel : BorelSpace F := ⟨rfl⟩
local instance adjacentRankModelMapGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F) := borel _

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
  (hself : IsSelfDual ψ ν) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)

/-- Smoothness suffices for convergence of the entire finite tensor integral. -/
theorem adjacentRankModelConverges_of_isSmooth (hσ : IsSmooth σ)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) (g : GeneralLinear (r + 2) F) :
    AdjacentRankModelConverges F ψ ν hself σ ℓ χ Ψ g := by
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    exact adjacentRankModelConverges_tmul_of_isSmooth F ψ ν hself r σ hσ ℓ χ Φ W g
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    exact RankinSelberg.AdjacentRankModelConverges.add h₁ h₂

/-- The literal integral as a linear map on the whole algebraic test space.
The smoothness proof supplies additivity via unconditional convergence. -/
def adjacentRankModelMap (hσ : IsSmooth σ) :
    adjacentRankTestSpace ψ σ ℓ →ₗ[ℂ] (GeneralLinear (r + 2) F → ℂ) where
  toFun Ψ := adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ
  map_add' Ψ₁ Ψ₂ := by
    funext g
    exact RankinSelberg.adjacentRankModelIntegral_add
      (adjacentRankModelConverges_of_isSmooth F ψ ν hself σ ℓ χ hσ Ψ₁ g)
      (adjacentRankModelConverges_of_isSmooth F ψ ν hself σ ℓ χ hσ Ψ₂ g)
  map_smul' c Ψ := by
    funext g
    exact RankinSelberg.adjacentRankModelIntegral_smul c Ψ

@[simp] theorem adjacentRankModelMap_apply (hσ : IsSmooth σ)
    (Ψ : adjacentRankTestSpace ψ σ ℓ) (g : GeneralLinear (r + 2) F) :
    adjacentRankModelMap F ψ ν hself σ ℓ χ hσ Ψ g =
      adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ g := rfl

/-- Right translation of the ambient variable agrees with `ρ₀` on the
tensor and the prescribed outer character and determinant factors. -/
theorem adjacentRankModelIntegral_mul (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (g k : GeneralLinear (r + 2) F) :
    adjacentRankModelIntegral F ψ ν hself σ ℓ χ Ψ (g * k) =
      (χ (GeneralLinear.determinant k) : ℂ) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          k (((r + 1 : ℕ) : ℂ) / 2) *
        adjacentRankModelIntegral F ψ ν hself σ ℓ χ
          (adjacentRankRho0 ψ ν hself σ ℓ k Ψ) g := by
  unfold adjacentRankModelIntegral RankinSelberg.adjacentRankModelIntegral
  simp only [map_mul, Units.val_mul, determinantWeight_mul,
    RankinSelberg.adjacentRankModelIntegrand, Module.End.mul_apply]
  ring

end Padic

end Langlands.AllField.RankinSelberg
