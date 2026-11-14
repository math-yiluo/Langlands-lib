import Langlands.Representation.RankinSelberg.AdjacentRankMatchedInnerSlices
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankDualCompactCoefficients
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankInnerSliceSeparation
/-! Matched original and transformed inner determinant-slice expansions. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualInnerSliceIntegral adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankModelIntegral compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuous_adjacentRankInnerSliceWeight dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel exists_adjacentRankInner_subgroup hasCompactSupport_adjacentRankInnerSliceWeight innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelConverges EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement IsPadicPairGammaFactor LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance matchedInnerGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F) := borel _
local instance matchedInnerGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance matchedInnerGroupSecondCountable (r : ℕ) :
    SecondCountableTopology (GeneralLinear (r + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (r + 1)
local instance matchedInnerGroupSigmaCompact (r : ℕ) :
    SigmaCompactSpace (GeneralLinear (r + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (r + 1)

/-- The literal transformed inner determinant-slice integral. -/
def adjacentRankDualInnerSliceIntegral {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (χ : Quasicharacter F) (j : ℤ) (s : ℂ)
    (W : GeneralLinear (r + 1) F → ℂ)
    (g : GeneralLinear (r + 1) F) : ℂ :=
  ∫ h, adjacentRankInnerSliceWeight F Φ χ j s h * dualFunction r W (g * h)
    ∂generalLinearHaar F r

private theorem integral_sum_of_normalized_average {r N : ℕ}
    (K : OpenSubgroup (GeneralLinear (r + 1) F))
    (hKc : IsCompact (K : Set (GeneralLinear (r + 1) F)))
    (a v : GeneralLinear (r + 1) F → ℂ) (c : Fin N → ℂ)
    (f : Fin N → GeneralLinear (r + 1) F → ℂ)
    (ha : ∀ k ∈ K, ∀ h, a (k * h) = a h)
    (hv : Integrable (fun h => a h * v h) (generalLinearHaar F r))
    (hf : ∀ i, Integrable (fun h => a h * f i h) (generalLinearHaar F r))
    (havg : ∀ h, ((generalLinearHaar F r).real (K : Set _) : ℂ)⁻¹ *
      (∫ k in (K : Set _), v (k * h) ∂generalLinearHaar F r) =
        ∑ i, c i * f i h) :
    (∫ h, a h * v h ∂generalLinearHaar F r) =
      ∑ i, c i * ∫ h, a h * f i h ∂generalLinearHaar F r := by
  let η := generalLinearHaar F r
  let mass : ℂ := η.real (K : Set _)
  have hmass : mass ≠ 0 :=
    Langlands.AllField.GodementJacquet.Padic.measureReal_openSubgroup_ne_zero F K hKc
  obtain ⟨_, hval⟩ := GodementJacquet.leftAverage_integral η (K : Set _)
    K.isOpen.measurableSet hKc.measure_lt_top.ne a v ha hv
  have hnorm :
      (∫ h, a h * (mass⁻¹ * ∫ k in (K : Set _), v (k * h) ∂η) ∂η) =
        ∫ h, a h * v h ∂η := by
    calc
      _ = mass⁻¹ * ∫ h, a h * (∫ k in (K : Set _), v (k * h) ∂η) ∂η := by
        rw [← integral_const_mul]
        congr 1
        funext h
        ring
      _ = _ := by rw [hval, ← mul_assoc, inv_mul_cancel₀ hmass, one_mul]
  calc
    _ = ∫ h, a h * (mass⁻¹ * ∫ k in (K : Set _), v (k * h) ∂η) ∂η := hnorm.symm
    _ = ∫ h, ∑ i, c i * (a h * f i h) ∂η := by
      apply integral_congr_ae
      filter_upwards [] with h
      rw [havg h, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by
      rw [integral_finsetSum Finset.univ (fun i _ => (hf i).const_mul _)]
      simp only [integral_const_mul]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1600000 in
/-- A common averaging subgroup gives simultaneous original and transformed
inner slice expansions with exactly the same finite family and matrix
coefficients, for any two fixed square tests and determinant characters. -/
theorem adjacentRankInnerSlice_matchedFiniteSeparation
    (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsAdmissible σ) (ℓ : glFunctionals ψ r σ)
    (Φ ΦD : GodementJacquet.MatrixTestFunction r F)
    (χ χD : Quasicharacter F) :
    ∃ (N : ℕ) (B : Fin N → (glCoefficientModel ψ r σ ℓ).toSubmodule),
      ∀ W : (glCoefficientModel ψ r σ ℓ).toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ),
          ∀ (j : ℤ) (s : ℂ) (g : GeneralLinear (r + 1) F),
            Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j s h *
              W.val.val (g * h)) (generalLinearHaar F r) ∧
            Integrable (fun h => adjacentRankInnerSliceWeight F ΦD χD j s h *
              dualFunction r W.val.val (g * h)) (generalLinearHaar F r) ∧
            (∀ i, Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j s h * (f i).val h)
                (generalLinearHaar F r) ∧
              Integrable (fun h => adjacentRankInnerSliceWeight F ΦD χD j s h *
                GodementJacquet.coefficientIota (f i).val h) (generalLinearHaar F r)) ∧
            (∫ h, adjacentRankInnerSliceWeight F Φ χ j s h * W.val.val (g * h)
              ∂generalLinearHaar F r) =
                ∑ i, (B i).val.val g *
                  ∫ h, adjacentRankInnerSliceWeight F Φ χ j s h * (f i).val h
                    ∂generalLinearHaar F r ∧
            adjacentRankDualInnerSliceIntegral F ΦD χD j s W.val.val g =
              ∑ i, (dualModelLinearMap ψ σ ℓ (B i)).val.val g *
                ∫ h, adjacentRankInnerSliceWeight F ΦD χD j s h *
                  GodementJacquet.coefficientIota (f i).val h ∂generalLinearHaar F r := by
  obtain ⟨K₀, hK₀c, hK₀ι, hK₀⟩ := exists_adjacentRankInner_subgroup F Φ χ
  obtain ⟨K₁, _, hK₁ι, hK₁⟩ := exists_adjacentRankInner_subgroup F ΦD χD
  let K := K₀ ⊓ K₁
  have hKc : IsCompact (K : Set (GeneralLinear (r + 1) F)) :=
    hK₀c.inter_right K₁.isClosed
  have hKι : ∀ k ∈ K, inverseTranspose (r + 1) F k ∈ K :=
    fun k hk => ⟨hK₀ι k hk.1, hK₁ι k hk.2⟩
  obtain ⟨N, B, hB⟩ := adjacentRankCompact_middleAverage_and_dual F ψ σ hσ ℓ K hKc hKι
  refine ⟨N, B, fun W => ?_⟩
  obtain ⟨f, hfo, hfd⟩ := hB W
  refine ⟨f, fun j s g => ?_⟩
  have hWc := glModelFunction_continuous ψ r σ hσ.1 ℓ W
  have hWdc : Continuous (dualFunction r W.val.val) := by
    change Continuous (fun h => W.val.val
      (weylLong (r + 1) F * inverseTranspose (r + 1) F h))
    exact hWc.comp (continuous_const.mul (continuous_inverseTranspose (r + 1) F))
  have hWo := integrable_adjacentRankInnerSliceWeight_mul F Φ χ j s
    (fun h => W.val.val (g * h))
    (hWc.comp (continuous_const.mul continuous_id))
  have hWd := integrable_adjacentRankInnerSliceWeight_mul F ΦD χD j s
    (fun h => dualFunction r W.val.val (g * h))
    (hWdc.comp (continuous_const.mul continuous_id))
  have hfc (i : Fin N) : Continuous (f i).val :=
    (GodementJacquet.isLocallyConstant_biSmoothMatrixCoefficients _ (f i)).continuous
  have hfi (i : Fin N) := integrable_adjacentRankInnerSliceWeight_mul F Φ χ j s _ (hfc i)
  have hfdi (i : Fin N) := integrable_adjacentRankInnerSliceWeight_mul F ΦD χD j s _
    ((hfc i).comp (continuous_inverseTranspose (r + 1) F))
  refine ⟨hWo, hWd, fun i => ⟨hfi i, hfdi i⟩, ?_, ?_⟩
  · refine integral_sum_of_normalized_average F K hKc
      (adjacentRankInnerSliceWeight F Φ χ j s) (fun h => W.val.val (g * h))
      (fun i => (B i).val.val g) (fun i => (f i).val) ?_ hWo hfi ?_
    · intro k hk h
      obtain ⟨hΦ, hχ, hdet⟩ := hK₀ k hk.1
      exact adjacentRankInnerSliceWeight_mul F Φ χ k hΦ hχ hdet j s h
    · intro h
      simpa only [mul_assoc] using hfo g h
  · refine integral_sum_of_normalized_average F K hKc
      (adjacentRankInnerSliceWeight F ΦD χD j s)
      (fun h => dualFunction r W.val.val (g * h))
      (fun i => (dualModelLinearMap ψ σ ℓ (B i)).val.val g)
      (fun i => GodementJacquet.coefficientIota (f i).val) ?_ hWd hfdi ?_
    · intro k hk h
      obtain ⟨hΦ, hχ, hdet⟩ := hK₁ k hk.2
      exact adjacentRankInnerSliceWeight_mul F ΦD χD k hΦ hχ hdet j s h
    · intro h
      simpa only [adjacentRankDualMiddleAverage, mul_assoc] using hfd g h

end Langlands.AllField.RankinSelberg.Padic
