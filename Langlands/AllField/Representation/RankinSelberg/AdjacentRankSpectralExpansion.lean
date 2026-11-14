import Langlands.Representation.RankinSelberg.AdjacentRankSpectralExpansion
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankInnerSliceSeparation
import Langlands.AllField.Representation.RankinSelberg.AnalyticBridge
import Langlands.AllField.Representation.RankinSelberg.EqualRankSliceExpansionProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
/-! Spectral expansion of the actual adjacent-rank finite coefficient formula. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open scoped BigOperators

universe uF uV uW

namespace Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges adjacentRankCompact_middleAverage adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankMatrixSliceCoefficient adjacentRankMatrixSliceExpansion adjacentRankModelIntegral compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuous_adjacentRankInnerSliceWeight corankOneIntegrand_eq_mul_spectralPoint_zpow corankOneSliceExpansion exists_adjacentRankInner_subgroup hasCompactSupport_adjacentRankInnerSliceWeight hasSum_setIntegral_generalLinearDeterminantSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul setIntegral_matrixIntegrand_determinantSlice spectralFieldTopology spectralFieldValuation spectralGroupBorelSpace spectralGroupMeasurableSpace spectralLocalField spectralQuotientBorelSpace spectralQuotientMeasurableSpace
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelConverges EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance spectralGroupMeasurableSpace (r : ℕ) : MeasurableSpace
    (Langlands.GeneralLinear (r + 1) F) := borel _
local instance spectralGroupBorelSpace (r : ℕ) : BorelSpace
    (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance spectralQuotientMeasurableSpace (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F) := borel _
local instance spectralQuotientBorelSpace (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

/-- The group determinant coefficient in the actual finite model formula. -/
def adjacentRankMatrixSliceCoefficient {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (χ : Quasicharacter F)
    (f : Langlands.GeneralLinear (r + 1) F → ℂ) (m : ℤ) : ℂ :=
  ∫ h, adjacentRankInnerSliceWeight F Φ χ m ((r : ℂ) / 2) h * f h
    ∂generalLinearHaar F r

/-- The actual general-linear determinant fibers partition every convergent
matrix integral. -/
theorem hasSum_setIntegral_generalLinearDeterminantSlice {r : ℕ}
    (η : Measure (Langlands.GeneralLinear (r + 1) F))
    {f : Langlands.GeneralLinear (r + 1) F → ℂ}
    (hf : Integrable f η) :
    HasSum (fun m : ℤ => ∫ h in generalLinearDeterminantSlice
      (⟨⟩ : LocalFieldData F) r m, f h ∂η) (∫ h, f h ∂η) := by
  have hcover : (⋃ m : ℤ, generalLinearDeterminantSlice
      (⟨⟩ : LocalFieldData F) r m) = Set.univ := by
    ext h
    simp only [Set.mem_iUnion, mem_generalLinearDeterminantSlice, Set.mem_univ,
      iff_true]
    exact ⟨_, rfl⟩
  have hdisj : Pairwise (fun i j => Disjoint
      (generalLinearDeterminantSlice (⟨⟩ : LocalFieldData F) r i)
      (generalLinearDeterminantSlice (⟨⟩ : LocalFieldData F) r j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro h hi hj
    exact hij (hi.symm.trans hj)
  have h := hasSum_integral_iUnion
    (fun m => (isClopen_generalLinearDeterminantSlice
      (⟨⟩ : LocalFieldData F) r m).isClosed.measurableSet)
    hdisj (by rw [hcover]; exact hf.integrableOn)
  rwa [hcover, Measure.restrict_univ] at h

/-- The actual shifted matrix integral has the same spectral convention as the
quotient integrals, with base exponent `r/2`. -/
theorem setIntegral_matrixIntegrand_determinantSlice {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (χ : Quasicharacter F)
    (f : Langlands.GeneralLinear (r + 1) F → ℂ) (m : ℤ) (s : ℂ) :
    (∫ h in generalLinearDeterminantSlice (⟨⟩ : LocalFieldData F) r m,
      GodementJacquet.matrixIntegrand abv Φ (s + (r : ℂ) / 2)
        (fun g => (χ (GeneralLinear.determinant g) : ℂ) * f g) h
          ∂generalLinearHaar F r) =
      adjacentRankMatrixSliceCoefficient F Φ χ f m * spectralPoint qF s ^ m := by
  let S := generalLinearDeterminantSlice (⟨⟩ : LocalFieldData F) r m
  have hS : MeasurableSet S :=
    (isClopen_generalLinearDeterminantSlice (⟨⟩ : LocalFieldData F) r m).isClosed.measurableSet
  have heq : ∀ h ∈ S,
      GodementJacquet.matrixIntegrand abv Φ (s + (r : ℂ) / 2)
        (fun g => (χ (GeneralLinear.determinant g) : ℂ) * f g) h =
      (Φ h.val * (χ (GeneralLinear.determinant h) : ℂ) *
        determinantWeight abv h ((r : ℂ) / 2) * f h) * spectralPoint qF s ^ m := by
    intro h hh
    have hw : determinantWeight abv h s = spectralPoint qF s ^ m := by
      rw [normalizedDeterminantWeight_eq_spectralPoint_zpow]
      change (⟨⟩ : LocalFieldData F).ord (Matrix.det h.val) = m at hh
      rw [hh]
    dsimp only [GodementJacquet.matrixIntegrand]
    rw [determinantWeight_exponent_add, hw]
    ring
  rw [setIntegral_congr_fun hS heq, integral_mul_const]
  congr 1
  rw [adjacentRankMatrixSliceCoefficient, ← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with h
  by_cases hh : h ∈ generalLinearDeterminantSlice (⟨⟩ : LocalFieldData F) r m
  · simp only [S, adjacentRankInnerSliceWeight, matrixSliceTest_apply,
      Set.indicator_of_mem hh]
  · simp only [S, adjacentRankInnerSliceWeight, matrixSliceTest_apply,
      Set.indicator_of_notMem hh, zero_mul]

/-- At each supplied convergent parameter the shifted matrix integral is the
absolutely summable series of the actual group coefficients. -/
theorem adjacentRankMatrixSliceExpansion {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (χ : Quasicharacter F)
    (f : Langlands.GeneralLinear (r + 1) F → ℂ) (s : ℂ)
    (hs : Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
      (fun g => (χ (GeneralLinear.determinant g) : ℂ) * f g)) :
    Summable (fun m : ℤ => ‖adjacentRankMatrixSliceCoefficient F Φ χ f m *
      spectralPoint qF s ^ m‖) ∧
      HasSum (fun m : ℤ => adjacentRankMatrixSliceCoefficient F Φ χ f m *
        spectralPoint qF s ^ m)
        (Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + (r : ℂ) / 2)
          (fun g => (χ (GeneralLinear.determinant g) : ℂ) * f g)) := by
  have h := hasSum_setIntegral_generalLinearDeterminantSlice F
    (generalLinearHaar F r) hs
  simp only [setIntegral_matrixIntegrand_determinantSlice F Φ χ f] at h
  exact ⟨summable_norm_iff.mpr h.summable, h⟩

/-- The actual corank-one integrand has the standard spectral weight on each
quotient determinant slice. -/
theorem corankOneIntegrand_eq_mul_spectralPoint_zpow {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (m : ℤ) (q : LeftUnipotentQuotient r F)
    (hq : q ∈ determinantSlice (⟨⟩ : LocalFieldData F) r m) (s : ℂ) :
    corankOneIntegrand ψ abv U W' s q =
      corankOneIntegrand ψ abv U W' 0 q * spectralPoint qF s ^ m := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [mk_mem_determinantSlice] at hq
    rw [corankOneIntegrand_mk, corankOneIntegrand_mk]
    have hexp : s - 1 / 2 = (0 - 1 / 2) + s := by ring
    have hw : determinantWeight abv g s = spectralPoint qF s ^ m := by
      rw [normalizedDeterminantWeight_eq_spectralPoint_zpow]
      change (⟨⟩ : LocalFieldData F).ord (Matrix.det g.val) = m at hq
      rw [hq]
    rw [hexp, determinantWeight_exponent_add, hw]
    ring

/-- At every convergent parameter the actual corank-one integral is the
absolutely summable series of its coefficients at zero. -/
theorem corankOneSliceExpansion {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (ν : Measure (LeftUnipotentQuotient r F)) (s : ℂ)
    (hs : Integrable (corankOneIntegrand ψ abv U W' s) ν) :
    Summable (fun m : ℤ => ‖sliceCoefficient (⟨⟩ : LocalFieldData F) ν
      (corankOneIntegrand ψ abv U W' 0) m * spectralPoint qF s ^ m‖) ∧
      HasSum (fun m : ℤ => sliceCoefficient (⟨⟩ : LocalFieldData F) ν
        (corankOneIntegrand ψ abv U W' 0) m * spectralPoint qF s ^ m)
        (∫ q, corankOneIntegrand ψ abv U W' s q ∂ν) := by
  have heq : ∀ m : ℤ,
      (∫ q in determinantSlice (⟨⟩ : LocalFieldData F) r m,
        corankOneIntegrand ψ abv U W' s q ∂ν) =
      sliceCoefficient (⟨⟩ : LocalFieldData F) ν
        (corankOneIntegrand ψ abv U W' 0) m * spectralPoint qF s ^ m := by
    intro m
    rw [setIntegral_congr_fun
      (measurableSet_determinantSlice (⟨⟩ : LocalFieldData F) r m)
      (fun q hq => corankOneIntegrand_eq_mul_spectralPoint_zpow F ψ U W' m q hq s),
      integral_mul_const]
    rfl
  exact ⟨by simpa only [heq] using
      summable_norm_setIntegral_determinantSlice (⟨⟩ : LocalFieldData F) ν hs,
    by simpa only [heq] using
      hasSum_setIntegral_determinantSlice (⟨⟩ : LocalFieldData F) ν hs⟩

end Padic
end Langlands.AllField.RankinSelberg
