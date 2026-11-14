import Langlands.Representation.RankinSelberg.AdjacentRankInnerSliceSeparation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankCompactCoefficients
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankDeterminantShells
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
/-! The inner determinant-slice separation of JPSS Section 6.3, (6)--(9). -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding ModelWhittakerRationalityStatement WhittakerModelComparisonStatement whittakerModelComparison_of_rationality
open Langlands.AllField.GodementJacquet

universe uG uV

end Langlands.AllField.GodementJacquet

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges adjacentRankCompact_middleAverage adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankModelIntegral compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuous_adjacentRankInnerSliceWeight exists_adjacentRankInner_subgroup hasCompactSupport_adjacentRankInnerSliceWeight innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelConverges EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open scoped BigOperators _root_.Topology

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance innerSliceGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F) := borel _
local instance innerSliceGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩

/-- A single compact open subgroup, stable under inverse transpose, fixes the
square test and is trivial under both determinant characters. -/
theorem exists_adjacentRankInner_subgroup {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (χ : Quasicharacter F) :
    ∃ K : OpenSubgroup (Langlands.GeneralLinear (r + 1) F),
      IsCompact (K : Set (Langlands.GeneralLinear (r + 1) F)) ∧
      (∀ k ∈ K, GeneralLinear.inverseTranspose (r + 1) F k ∈ K) ∧
      ∀ k ∈ K,
        (∀ M, Φ (k.val * M) = Φ M) ∧
        χ (GeneralLinear.determinant k) = 1 ∧
        (⟨⟩ : LocalFieldData F).normalizedAbs (Matrix.det k.val) = 1 := by
  let T := (⟨⟩ : LocalFieldData F)
  let G := Langlands.GeneralLinear (r + 1) F
  let := T.generalLinearNonarchimedean (r + 1)
  let θ : G →* ℂˣ := (χ : Fˣ →* ℂˣ).comp GeneralLinear.determinant
  have hθ : IsOpen (θ.ker : Set G) :=
    isOpen_ker_of_continuous_complex_character θ
      (χ.continuous.comp (T.generalLinearDeterminant (r + 1)).continuous)
  obtain ⟨U, hUc, hU⟩ :=
    Langlands.AllField.GodementJacquet.Padic.exists_compactOpen_matrixTest_invariant F Φ
  let C : OpenSubgroup G := ⟨θ.ker, hθ⟩
  let L := U ⊓ C
  let Li := L.comap (GeneralLinear.inverseTranspose (r + 1) F).toMonoidHom
    (GeneralLinear.continuous_inverseTranspose (r + 1) F)
  let K := L ⊓ Li
  have hLc : IsCompact (L : Set G) := hUc.inter_right C.isClosed
  refine ⟨K, hLc.inter_right Li.isClosed, ?_, ?_⟩
  · intro k hk
    exact ⟨hk.2, by
      change GeneralLinear.inverseTranspose (r + 1) F
        (GeneralLinear.inverseTranspose (r + 1) F k) ∈ L
      rw [GeneralLinear.inverseTranspose_involutive]
      exact hk.1⟩
  · intro k hk
    exact ⟨(hU k hk.1.1).1, hk.1.2, (hU k hk.1.1).2⟩

/-- The actual compactly supported weight in the inner determinant-slice
integral, for every order and every complex exponent. -/
def adjacentRankInnerSliceWeight {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (χ : Quasicharacter F) (j : ℤ) (s : ℂ)
    (h : Langlands.GeneralLinear (r + 1) F) : ℂ :=
  matrixSliceTest (⟨⟩ : LocalFieldData F) r Φ j h *
    (χ (GeneralLinear.determinant h) : ℂ) *
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) h s

theorem continuous_adjacentRankInnerSliceWeight {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (χ : Quasicharacter F) (j : ℤ) (s : ℂ) :
    Continuous (adjacentRankInnerSliceWeight F Φ χ j s) := by
  exact (((matrixSliceTest (⟨⟩ : LocalFieldData F) r Φ j).continuous.mul
    (Units.continuous_val.comp (χ.continuous.comp
      ((⟨⟩ : LocalFieldData F).generalLinearDeterminant (r + 1)).continuous))).mul
    (continuous_adjacentRank_determinantWeight F (r + 1) s))

theorem hasCompactSupport_adjacentRankInnerSliceWeight {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (χ : Quasicharacter F) (j : ℤ) (s : ℂ) :
    HasCompactSupport (adjacentRankInnerSliceWeight F Φ χ j s) :=
  (matrixSliceTest (⟨⟩ : LocalFieldData F) r Φ j).hasCompactSupport.mul_right.mul_right

/-- Slice integrability holds for every continuous coefficient, with no growth
or right-half-plane premise. -/
theorem integrable_adjacentRankInnerSliceWeight_mul {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (χ : Quasicharacter F) (j : ℤ) (s : ℂ)
    (f : Langlands.GeneralLinear (r + 1) F → ℂ) (hf : Continuous f) :
    Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j s h * f h)
      (generalLinearHaar F r) :=
  ((continuous_adjacentRankInnerSliceWeight F Φ χ j s).mul hf).integrable_of_hasCompactSupport
    (hasCompactSupport_adjacentRankInnerSliceWeight F Φ χ j s).mul_right

/-- The character and test conditions on the averaging subgroup make the
complete slice weight left invariant. -/
theorem adjacentRankInnerSliceWeight_mul {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (χ : Quasicharacter F)
    (k : Langlands.GeneralLinear (r + 1) F)
    (hΦ : ∀ M, Φ (k.val * M) = Φ M)
    (hχ : χ (GeneralLinear.determinant k) = 1)
    (hdet : (⟨⟩ : LocalFieldData F).normalizedAbs (Matrix.det k.val) = 1)
    (j : ℤ) (s : ℂ) (h : Langlands.GeneralLinear (r + 1) F) :
    adjacentRankInnerSliceWeight F Φ χ j s (k * h) =
      adjacentRankInnerSliceWeight F Φ χ j s h := by
  let T := (⟨⟩ : LocalFieldData F)
  have hord : T.ord (GeneralLinear.determinant k : F) = 0 :=
    (T.ord_eq_zero_iff_normalizedAbs (GeneralLinear.determinant k)).mpr hdet
  have hs : k * h ∈ generalLinearDeterminantSlice T r j ↔
      h ∈ generalLinearDeterminantSlice T r j := by
    simp only [mem_generalLinearDeterminantSlice, map_mul, Units.val_mul]
    rw [T.ord_mul (GeneralLinear.determinant k).ne_zero
      (GeneralLinear.determinant h).ne_zero, hord, zero_add]
  have hw : determinantWeight (normalizedAbsoluteValue T) (k * h) s =
      determinantWeight (normalizedAbsoluteValue T) h s := by
    simp only [determinantWeight, Units.val_mul, Matrix.det_mul, AbsoluteValue.map_mul]
    rw [show normalizedAbsoluteValue T (Matrix.det k.val) = 1 from hdet, one_mul]
  by_cases hh : h ∈ generalLinearDeterminantSlice T r j
  · have hkh := hs.mpr hh
    dsimp only [T] at hh hkh hw
    simp only [adjacentRankInnerSliceWeight, matrixSliceTest_apply,
      Set.indicator_of_mem hh, Set.indicator_of_mem hkh, Units.val_mul, hΦ,
      map_mul, hχ, one_mul, hw]
  · have hkh : k * h ∉ generalLinearDeterminantSlice T r j := fun he => hh (hs.mp he)
    dsimp only [T] at hh hkh
    simp only [adjacentRankInnerSliceWeight, matrixSliceTest_apply,
      Set.indicator_of_notMem hh, Set.indicator_of_notMem hkh, zero_mul]

end Langlands.AllField.RankinSelberg.Padic
