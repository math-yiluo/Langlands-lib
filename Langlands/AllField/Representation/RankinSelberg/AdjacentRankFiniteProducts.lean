import Langlands.Representation.RankinSelberg.AdjacentRankFiniteProducts
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelZetaCoefficient
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankSpectralExpansion
/-! The actual finite integral product identity at a common convergent parameter. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCompact_middleAverage adjacentRankFiniteProductValue adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankMatrixSliceCoefficient adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound adjacentRankMatrixSliceExpansion adjacentRankModelIntegral adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_shear_fubini compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel corankOneIntegral_eq_finiteProducts_of_coefficients corankOneIntegrand_eq_mul_spectralPoint_zpow corankOneSliceExpansion equalRankSliceCoefficient_eq_zero_of_pointwise_bound exists_adjacentRankInner_subgroup exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice hasSum_setIntegral_generalLinearDeterminantSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel productsFieldTopology productsQuotientMeasurableSpace quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel setIntegral_matrixIntegrand_determinantSlice shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel spectralFieldTopology spectralFieldValuation spectralGroupBorelSpace spectralGroupMeasurableSpace spectralLocalField spectralQuotientBorelSpace spectralQuotientMeasurableSpace
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelConverges EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceExpansionStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open scoped BigOperators

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance productsQuotientMeasurableSpace (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F) := borel _

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)
local notation "qF" => (Langlands.LocalFieldData.residueCardinality (⟨⟩ : LocalFieldData F))

/-- The literal finite sum of equal-rank and shifted matrix integrals. -/
def adjacentRankFiniteProductValue {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (W : WhittakerFunctions ψ r) (B : Fin N → InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (χ : Quasicharacter F)
    (f : Fin N → Langlands.GeneralLinear (r + 1) F → ℂ) (s : ℂ) : ℂ :=
  ∑ i, equalRankIntegral ψ abv ν W (B i) φ s *
    Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + (r : ℂ) / 2)
      (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h)

/-- A pointwise lower determinant bound forces every smaller quotient coefficient
to vanish, independently of the second Whittaker function. -/
theorem equalRankSliceCoefficient_eq_zero_of_pointwise_bound {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (φ : SchwartzBruhat (Fin (r + 1) → F)) (L : ℤ)
    (hL : ∀ g, W.val g ≠ 0 → φ (lastRow g) ≠ 0 →
      L ≤ (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F))
    (m : ℤ) (hm : m < L) :
    equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) ν ψ W W' φ m = 0 := by
  rw [equalRankSliceCoefficient_def]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro q hq
  induction q using Quotient.inductionOn with
  | h g =>
    rw [mk_mem_determinantSlice] at hq
    rw [equalRankIntegrand_zero_mk]
    by_cases hW : W.val g = 0
    · rw [hW, zero_mul, zero_mul]
    by_cases hφ : φ (lastRow g) = 0
    · rw [hφ, mul_zero]
    have hb := hL g hW hφ
    omega

/-- The square-test support bound forces all smaller group coefficients to vanish.
No global convergence is needed for this support assertion. -/
theorem adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (χ : Quasicharacter F)
    (f : Langlands.GeneralLinear (r + 1) F → ℂ) (L : ℤ)
    (hL : ∀ h : Langlands.GeneralLinear (r + 1) F, Φ h.val ≠ 0 →
      L ≤ (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant h : F))
    (m : ℤ) (hm : m < L) :
    adjacentRankMatrixSliceCoefficient F Φ χ f m = 0 := by
  rw [adjacentRankMatrixSliceCoefficient]
  apply integral_eq_zero_of_ae
  filter_upwards [] with h
  dsimp only [adjacentRankInnerSliceWeight]
  rw [matrixSliceTest_apply]
  by_cases hh : h ∈ generalLinearDeterminantSlice (⟨⟩ : LocalFieldData F) r m
  · rw [Set.indicator_of_mem hh]
    have hΦ : Φ h.val = 0 := by
      by_contra hne
      have hb := hL h hne
      change (⟨⟩ : LocalFieldData F).ord
        (GeneralLinear.determinant h : F) = m at hh
      omega
    rw [hΦ, zero_mul, zero_mul, zero_mul]
    rfl
  · rw [Set.indicator_of_notMem hh, zero_mul, zero_mul, zero_mul]
    rfl

/-- A finite coefficient convolution gives the actual integral identity whenever
all the actual integrals converge at the same supplied parameter. -/
theorem corankOneIntegral_eq_finiteProducts_of_coefficients {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (W : WhittakerFunctions ψ r) (B : Fin N → InverseWhittakerFunctions ψ r)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (χ : Quasicharacter F)
    (f : Fin N → Langlands.GeneralLinear (r + 1) F → ℂ)
    (Lq Lh : ℤ)
    (hLq : ∀ g, W.val g ≠ 0 → φ (lastRow g) ≠ 0 →
      Lq ≤ (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F))
    (hLh : ∀ h : Langlands.GeneralLinear (r + 1) F, Φ h.val ≠ 0 →
      Lh ≤ (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant h : F))
    (hc : ∀ m : ℤ, sliceCoefficient (⟨⟩ : LocalFieldData F) ν
      (corankOneIntegrand ψ abv U W' 0) m =
      ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
        equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) ν ψ W (B i) φ k *
          adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k))
    (s : ℂ)
    (hU : CorankOneConverges ψ abv ν U W' s)
    (hW : ∀ i, EqualRankConverges ψ abv ν W (B i) φ s)
    (hf : ∀ i, Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
      (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h)) :
    corankOneIntegral ψ abv ν U W' s =
      adjacentRankFiniteProductValue F ψ ν W B Φ φ χ f s := by
  classical
  have hi : ∀ i : Fin N,
      HasSum (fun m : ℤ =>
        (∑ k ∈ Finset.Icc Lq (m - Lh),
          equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) ν ψ W (B i) φ k *
            adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k)) *
              spectralPoint qF s ^ m)
        (equalRankIntegral ψ abv ν W (B i) φ s *
          Langlands.AllField.GodementJacquet.Padic.matrixIntegral F Φ (s + (r : ℂ) / 2)
            (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h)) := by
    intro i
    exact (hasSum_intervalConvolution _ _ Lq Lh
      (equalRankSliceCoefficient_eq_zero_of_pointwise_bound F ψ ν W (B i) φ Lq hLq)
      (adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound F Φ χ (f i) Lh hLh)
      _ _ _ (spectralPoint_ne_zero_of_pos
        (lt_trans Nat.zero_lt_one (⟨⟩ : LocalFieldData F).residueCardinality_gt_one) s)
      (equalRankSliceExpansion F (⟨⟩ : LocalFieldData F) r ν ψ W (B i) φ s (hW i)).2.2
      (adjacentRankMatrixSliceExpansion F Φ χ (f i) s (hf i)).2).2
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => hi i)
  have heq : (fun m : ℤ => ∑ i : Fin N,
      (∑ k ∈ Finset.Icc Lq (m - Lh),
        equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) ν ψ W (B i) φ k *
          adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k)) *
            spectralPoint qF s ^ m) =
      (fun m : ℤ => sliceCoefficient (⟨⟩ : LocalFieldData F) ν
        (corankOneIntegrand ψ abv U W' 0) m * spectralPoint qF s ^ m) := by
    funext m
    rw [← Finset.sum_mul, Finset.sum_comm, ← hc m]
  rw [heq] at hsum
  exact (corankOneSliceExpansion F ψ U W' ν s hU).2.unique hsum


end Langlands.AllField.RankinSelberg.Padic
