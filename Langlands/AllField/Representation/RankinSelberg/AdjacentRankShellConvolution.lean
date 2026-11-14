import Langlands.Representation.RankinSelberg.AdjacentRankShellConvolution
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankInnerSliceSeparation
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankQuotientShear
import Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement
/-! The finite determinant-shell convolution in JPSS Section 6.3, (8)--(10). -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCompact_middleAverage adjacentRankInnerMultiplier adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankModelIntegral adjacentRankShell_shear_fubini compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel exists_adjacentRankInner_subgroup exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelConverges EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open scoped BigOperators _root_.Topology

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance shellConvolutionQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F) := borel _
local instance shellConvolutionQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F) := ⟨rfl⟩

/-- The actual continuous character and norm multiplier in the inner integral. -/
def adjacentRankInnerMultiplier {r : ℕ} (χ : Quasicharacter F) (s : ℂ)
    (h : Langlands.GeneralLinear (r + 1) F) : ℂ :=
  (χ (GeneralLinear.determinant h) : ℂ) *
    determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) h s

theorem continuous_adjacentRankInnerMultiplier {r : ℕ}
    (χ : Quasicharacter F) (s : ℂ) :
    Continuous (adjacentRankInnerMultiplier F (r := r) χ s) :=
  (Units.continuous_val.comp (χ.continuous.comp
    ((⟨⟩ : LocalFieldData F).generalLinearDeterminant (r + 1)).continuous)).mul
      (continuous_adjacentRank_determinantWeight F (r + 1) s)

/-- The equal-rank integrand at zero has compact support on every quotient
slice when its first member is an actual smooth coefficient-image vector. -/
theorem hasCompactSupport_equalRankSlice {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r)
    (φ : SchwartzBruhat (Fin (r + 1) → F)) (k : ℤ) :
    HasCompactSupport ((determinantSlice (⟨⟩ : LocalFieldData F) r k).indicator
      (equalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        W.val W' φ 0)) := by
  have hc := whittakerRowSliceCompactSupport F (⟨⟩ : LocalFieldData F) r ψ V σ hσ ℓ W φ k
  apply hc.mono
  intro q hq
  rw [Function.mem_support, Set.indicator_apply_ne_zero] at hq ⊢
  refine ⟨hq.1, ?_⟩
  induction q using Quotient.inductionOn with
  | h g =>
    have hv : equalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        W.val W' φ 0 (Quotient.mk _ g) ≠ 0 := hq.2
    rw [equalRankIntegrand_zero_mk] at hv
    change ‖W.val.val g‖ * ‖φ (lastRow g)‖ ≠ 0
    exact mul_ne_zero (norm_ne_zero_iff.mpr (mul_ne_zero_iff.mp
      (mul_ne_zero_iff.mp hv).1).1)
      (norm_ne_zero_iff.mpr (mul_ne_zero_iff.mp hv).2)

/-- In particular every such equal-rank slice is genuinely integrable against
any Borel quotient measure finite on compact sets. -/
theorem integrable_equalRankSlice {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r) (hW' : Continuous W'.val)
    (φ : SchwartzBruhat (Fin (r + 1) → F)) (k : ℤ)
    (ν : Measure (LeftUnipotentQuotient r F)) [IsFiniteMeasureOnCompacts ν] :
    Integrable ((determinantSlice (⟨⟩ : LocalFieldData F) r k).indicator
      (equalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        W.val W' φ 0)) ν := by
  have hcont : Continuous (equalRankIntegrand ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) W.val W' φ 0) := by
    apply (leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (r + 1) F)).isQuotientMap.continuous_iff.mpr
    change Continuous (fun g => W.val.val g * W'.val g * φ (lastRow g) *
      determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g 0)
    simp only [determinantWeight_zero, mul_one]
    exact Continuous.mul
      (f := fun g => W.val.val g * W'.val g)
      (g := fun g => φ (lastRow g))
      ((glModelFunction_continuous ψ r σ hσ ℓ W).mul hW')
      (φ.continuous.comp continuous_lastRow)
  exact ((isClopen_determinantSlice (⟨⟩ : LocalFieldData F) r k).continuous_indicator
    hcont).integrable_of_hasCompactSupport
      (hasCompactSupport_equalRankSlice F ψ σ hσ ℓ W W' φ k)

/-- A finite support bound in determinant order gives an exact finite partition
of the integral. The bound concerns actual pointwise support. -/
theorem integral_eq_sum_determinantSlices {r : ℕ}
    (ν : Measure (LeftUnipotentQuotient r F))
    (f : LeftUnipotentQuotient r F → ℂ) (hf : Integrable f ν)
    (I : Finset ℤ)
    (hI : ∀ q, f q ≠ 0 → determinantOrder (⟨⟩ : LocalFieldData F) r q ∈ I) :
    (∫ q, f q ∂ν) = ∑ k ∈ I,
      ∫ q, (determinantSlice (⟨⟩ : LocalFieldData F) r k).indicator f q ∂ν := by
  classical
  have heq : f = fun q => ∑ k ∈ I,
      (determinantSlice (⟨⟩ : LocalFieldData F) r k).indicator f q := by
    funext q
    by_cases hz : f q = 0
    · simp [Set.indicator_apply, hz]
    · symm
      rw [Finset.sum_eq_single (determinantOrder (⟨⟩ : LocalFieldData F) r q)]
      · exact Set.indicator_of_mem (show q ∈ determinantSlice
          (⟨⟩ : LocalFieldData F) r (determinantOrder (⟨⟩ : LocalFieldData F) r q)
          from rfl) _
      · intro k hk hne
        exact Set.indicator_of_notMem (fun he => hne he.symm) _
      · exact fun hn => (hn (hI q hz)).elim
  calc
    _ = ∫ q, ∑ k ∈ I, (determinantSlice (⟨⟩ : LocalFieldData F) r k).indicator f q ∂ν :=
      congrArg (fun g => ∫ q, g q ∂ν) heq
    _ = _ := integral_finsetSum I fun k _ =>
      hf.indicator (measurableSet_determinantSlice (⟨⟩ : LocalFieldData F) r k)

/-- On a fixed quotient slice, the joint cutoff is precisely the complementary
group slice. This is the pointwise identity underlying the convolution. -/
theorem adjacentRankJointShellKernel_mk_eq_innerSlice {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (χ : Quasicharacter F) (m k : ℤ) (s : ℂ)
    (g h : Langlands.GeneralLinear (r + 1) F)
    (hg : (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) = k) :
    adjacentRankJointShellKernel F ψ W W' Φ φ
        (adjacentRankInnerMultiplier F χ s) m (Quotient.mk _ g, h) =
      W.val g * φ (lastRow g) *
        (adjacentRankInnerSliceWeight F Φ χ (m - k) s h * W'.val (g * h)) := by
  rw [adjacentRankJointShellKernel_mk]
  simp only [adjacentRankInnerSliceWeight, matrixSliceTest_apply,
    adjacentRankInnerMultiplier]
  by_cases hh : (⟨⟩ : LocalFieldData F).ord
      (GeneralLinear.determinant h : F) = m - k
  · have hs : (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) +
        (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant h : F) = m := by
      omega
    rw [ite_eq_left hs, Set.indicator_of_mem (show h ∈
      generalLinearDeterminantSlice (⟨⟩ : LocalFieldData F) r (m - k) from hh)]
    ring
  · have hs : (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) +
        (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant h : F) ≠ m := by
      omega
    rw [ite_eq_right hs, Set.indicator_of_notMem (show h ∉
      generalLinearDeterminantSlice (⟨⟩ : LocalFieldData F) r (m - k) from hh)]
    simp only [zero_mul, mul_zero]

end Langlands.AllField.RankinSelberg.Padic
