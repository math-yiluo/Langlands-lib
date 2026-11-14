import Langlands.Representation.RankinSelberg.AdjacentRankMatchedShellConvolution
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankMatchedInnerSlices
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankShellConvolution
/-! Matched actual shell convolutions with a supplied finite inner expansion. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges AdjacentRankShellConvolutionAt AdjacentRankShellLowerBounds adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCompact_middleAverage adjacentRankCompact_middleAverage_and_dual adjacentRankDualInnerSliceIntegral adjacentRankDualMiddleAverage adjacentRankDualMiddleAverage_eq adjacentRankInnerMultiplier adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankInnerSlice_matchedFiniteSeparation adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankModelIntegral adjacentRankShell_finiteConvolution_of_innerSeparation adjacentRankShell_matchedFiniteConvolution adjacentRankShell_shear_fubini compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel dualCompactFieldTopology dualCompactGroupBorel dualCompactGroupMeasurable dualCompactLocalField dualCompactValuativeRel exists_adjacentRankInner_subgroup exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices inverseCoefficientAsScaledStandard isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel matchedInnerFieldTopology matchedInnerGroupBorel matchedInnerGroupMeasurable matchedInnerGroupSecondCountable matchedInnerGroupSigmaCompact matchedInnerLocalField matchedInnerValuativeRel matchedShellFieldT2 matchedShellFieldTopology matchedShellGroupBorel matchedShellGroupMeasurable matchedShellGroupSecondCountable matchedShellGroupSigmaCompact matchedShellLocalField matchedShellQuotientLocallyCompact matchedShellQuotientMeasurable matchedShellQuotientSecondCountable matchedShellUnipotentBorel matchedShellUnipotentMeasurable matchedShellValuativeRel quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelConverges EqualRankAnalyticStatement EqualRankContinuedFormsStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement IsPadicPairGammaFactor LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankContinuedForms equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedAbsoluteValue_det_eq_zpow normalizedDeterminantWeight_eq_spectralPoint_zpow padic_rowFourier_equivariance padic_row_instances padic_row_translate_exists pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierEquivarianceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open scoped BigOperators _root_.Topology

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance matchedShellFieldT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance matchedShellGroupMeasurable (r : ℕ) : MeasurableSpace
    (Langlands.GeneralLinear (r + 1) F) := borel _
local instance matchedShellGroupBorel (r : ℕ) : BorelSpace
    (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance matchedShellUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (GeneralLinear.upperUnipotent (r + 1) F) := borel _
local instance matchedShellUnipotentBorel (r : ℕ) : BorelSpace
    (GeneralLinear.upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance matchedShellQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F) := borel _
local instance matchedShellGroupSecondCountable (r : ℕ) : SecondCountableTopology
    (Langlands.GeneralLinear (r + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (r + 1)
local instance matchedShellGroupSigmaCompact (r : ℕ) : SigmaCompactSpace
    (Langlands.GeneralLinear (r + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (r + 1)
local instance matchedShellQuotientSecondCountable (r : ℕ) : SecondCountableTopology
    (LeftUnipotentQuotient r F) :=
  TopologicalSpace.Quotient.secondCountableTopology
    (leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (r + 1) F)).isOpenMap
local instance matchedShellQuotientLocallyCompact (r : ℕ) : LocallyCompactSpace
    (LeftUnipotentQuotient r F) :=
  leftQuotient_locallyCompactSpace _

/-- The actual finite shell convolution, including integrability of both
product kernels and all quotient and group slice factors. -/
def AdjacentRankShellConvolutionAt {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (χ : Quasicharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (Lq Lh : ℤ) (B : Fin N → InverseWhittakerFunctions ψ r)
    (f : Fin N → GeneralLinear (r + 1) F → ℂ) (m : ℤ) (s : ℂ) : Prop :=
  let a := adjacentRankInnerMultiplier F χ s
  let η := generalLinearHaar F r
  let after := adjacentRankJointShellKernel F ψ W W' Φ φ a m
  let before := adjacentRankBeforeShearKernel F ψ W W' Φ φ a m
  let rhs := ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
    equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) ν ψ W (B i) φ k *
      ∫ h, adjacentRankInnerSliceWeight F Φ χ (m - k) s h * f i h ∂η
  Integrable before (ν.prod η) ∧ Integrable after (ν.prod η) ∧
    (∀ k i, Integrable ((determinantSlice (⟨⟩ : LocalFieldData F) r k).indicator
      (equalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        W (B i) φ 0)) ν) ∧
    (∀ j i, Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j s h * f i h) η) ∧
    (∫ z, after z ∂ν.prod η) = rhs ∧
    (∫ q, ∫ h, before (q, h) ∂η ∂ν) = rhs

set_option maxHeartbeats 1600000 in
/-- Carry a supplied inner expansion through the actual quotient shear and
finite determinant partition, retaining its exact family and coefficients. -/
theorem adjacentRankShell_finiteConvolution_of_innerSeparation {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r) (hW' : Continuous W'.val)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (χ : Quasicharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν)
    (Lq Lh : ℤ)
    (hLq : ∀ g, W.val.val g ≠ 0 → φ (lastRow g) ≠ 0 →
      Lq ≤ (⟨⟩ : LocalFieldData F).ord (determinant g : F))
    (hLh : ∀ h : GeneralLinear (r + 1) F, Φ h.val ≠ 0 →
      Lh ≤ (⟨⟩ : LocalFieldData F).ord (determinant h : F))
    (B : Fin N → InverseWhittakerFunctions ψ r) (hB : ∀ i, Continuous (B i).val)
    (f : Fin N → GeneralLinear (r + 1) F → ℂ) (hfc : ∀ i, Continuous (f i))
    (hsep : ∀ (j : ℤ) (s : ℂ) (g : GeneralLinear (r + 1) F),
      (∫ h, adjacentRankInnerSliceWeight F Φ χ j s h * W'.val (g * h)
        ∂generalLinearHaar F r) =
      ∑ i, (B i).val g * ∫ h, adjacentRankInnerSliceWeight F Φ χ j s h * f i h
        ∂generalLinearHaar F r) :
    ∀ (m : ℤ) (s : ℂ),
      AdjacentRankShellConvolutionAt F ψ W.val W' Φ φ χ ν Lq Lh B f m s := by
  classical
  let := hν.regular
  intro m s
  dsimp only [AdjacentRankShellConvolutionAt]
  let η := generalLinearHaar F r
  let a := adjacentRankInnerMultiplier F (r := r) χ s
  let after := adjacentRankJointShellKernel F ψ W.val W' Φ φ a m
  let before := adjacentRankBeforeShearKernel F ψ W.val W' Φ φ a m
  let outer := fun q => ∫ h, after (q, h) ∂η
  let I := Finset.Icc Lq (m - Lh)
  obtain ⟨hb, ha, -, ho, -, hba, -⟩ :=
    adjacentRankShell_shear_fubini F ψ σ hσ ℓ W W' hW' Φ φ a
      (continuous_adjacentRankInnerMultiplier F χ s) m ν hν
  have hslice (k : ℤ) (i : Fin N) :
      Integrable ((determinantSlice (⟨⟩ : LocalFieldData F) r k).indicator
        (equalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
          W.val (B i) φ 0)) ν :=
    integrable_equalRankSlice F ψ σ hσ ℓ W (B i) (hB i) φ k ν
  have hfi (j : ℤ) (i : Fin N) : Integrable (fun h =>
      adjacentRankInnerSliceWeight F Φ χ j s h * f i h) η :=
    integrable_adjacentRankInnerSliceWeight_mul F Φ χ j s (f i) (hfc i)
  have hsupport (q : LeftUnipotentQuotient r F)
      (h : Langlands.GeneralLinear (r + 1) F) (hz : after (q, h) ≠ 0) :
      determinantOrder (⟨⟩ : LocalFieldData F) r q ∈ I := by
    induction q using Quotient.inductionOn with
    | h g =>
      change adjacentRankJointShellKernel F ψ W.val W' Φ φ a m
        (Quotient.mk _ g, h) ≠ 0 at hz
      rw [adjacentRankJointShellKernel_mk] at hz
      split_ifs at hz with hs
      · have htest := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1).2
        have hrow := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp
          (mul_ne_zero_iff.mp hz).1).1).2
        have hfirst := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp
          (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1).1).1).1
        have hq := hLq g hfirst hrow
        have hh := hLh h htest
        exact Finset.mem_Icc.mpr ⟨hq, by
          change (⟨⟩ : LocalFieldData F).ord
            (GeneralLinear.determinant g : F) ≤ m - Lh
          omega⟩
      · exact (hz rfl).elim
  have houterSupport (q : LeftUnipotentQuotient r F) (hz : outer q ≠ 0) :
      determinantOrder (⟨⟩ : LocalFieldData F) r q ∈ I := by
    by_contra hn
    apply hz
    exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun h =>
      by_contra fun hh => hn (hsupport q h hh))
  have hpoint (k : ℤ) :
      (determinantSlice (⟨⟩ : LocalFieldData F) r k).indicator outer =
        fun q => ∑ i, (determinantSlice (⟨⟩ : LocalFieldData F) r k).indicator
          (equalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
            W.val (B i) φ 0) q *
          ∫ h, adjacentRankInnerSliceWeight F Φ χ (m - k) s h * f i h ∂η := by
    funext q
    by_cases hk : q ∈ determinantSlice (⟨⟩ : LocalFieldData F) r k
    · rw [Set.indicator_of_mem hk]
      induction q using Quotient.inductionOn with
      | h g =>
        have hg : (⟨⟩ : LocalFieldData F).ord
            (GeneralLinear.determinant g : F) = k := hk
        have heq (h : Langlands.GeneralLinear (r + 1) F) :
            after (Quotient.mk _ g, h) =
              W.val.val g * φ (lastRow g) *
                (adjacentRankInnerSliceWeight F Φ χ (m - k) s h *
                  W'.val (g * h)) :=
          adjacentRankJointShellKernel_mk_eq_innerSlice F ψ W.val W' Φ φ χ m k s g h hg
        change (∫ h, after (Quotient.mk _ g, h) ∂η) = _
        rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul,
          hsep (m - k) s g, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Set.indicator_of_mem hk, equalRankIntegrand_zero_mk]
        change _ = W.val.val g * (B i).val g *
          φ (lastRow g) * _
        ring
    · simp only [Set.indicator_of_notMem hk, zero_mul, Finset.sum_const_zero]
  have hconv :
      (∫ z, after z ∂ν.prod η) = ∑ k ∈ I, ∑ i,
        equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) ν ψ W.val (B i) φ k *
          ∫ h, adjacentRankInnerSliceWeight F Φ χ (m - k) s h * f i h ∂η := by
    rw [integral_prod _ ha, integral_eq_sum_determinantSlices F ν outer ho I houterSupport]
    apply Finset.sum_congr rfl
    intro k _
    rw [hpoint k, integral_finsetSum Finset.univ (fun i _ => (hslice k i).mul_const _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_mul_const]
    congr 1
    exact (sliceCoefficient_eq_integral_indicator (⟨⟩ : LocalFieldData F) ν
      (equalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        W.val (B i) φ 0) k).symm
  refine ⟨hb, ha, hslice, hfi, hconv, ?_⟩
  exact hba.trans ((integral_prod _ ha).symm.trans hconv)

/-- Recast the actual image of a specified inverse-character functional as
the image of its scaled-standard transport, retaining the same function. -/
def inverseCoefficientAsScaledStandard {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (ℓ : glInverseFunctionals ψ r σ)
    (W : (coefficientModel σ ℓ).toSubmodule) :
    (glCoefficientModel (ψ.scale (-1)) r σ
      (functionalsCongr (standardCharacter_scale_neg_one ψ r).symm ℓ)).toSubmodule :=
  ⟨InducedTailIntermediate.inverseAsScaledStandard ψ W.val, by
    obtain ⟨v, hv⟩ := W.property
    refine ⟨v, Subtype.ext ?_⟩
    exact congrArg (fun w : InverseWhittakerFunctions ψ r => w.val) hv⟩

/-- The actual pointwise lower support bounds used for a finite convolution. -/
def AdjacentRankShellLowerBounds {r : ℕ}
    (W : GeneralLinear (r + 1) F → ℂ)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F)) (Lq Lh : ℤ) : Prop :=
  (∀ g, W g ≠ 0 → φ (lastRow g) ≠ 0 →
    Lq ≤ (⟨⟩ : LocalFieldData F).ord (determinant g : F)) ∧
  (∀ h : GeneralLinear (r + 1) F, Φ h.val ≠ 0 →
    Lh ≤ (⟨⟩ : LocalFieldData F).ord (determinant h : F))

set_option maxHeartbeats 1600000 in
/-- Original and transformed outer convolutions use one actual finite model
family and exactly the same matrix coefficients, transformed by iota. -/
theorem adjacentRankShell_matchedFiniteConvolution {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (τ : Representation ℂ (GeneralLinear (r + 1) F) V')
    (hτ : IsAdmissible τ) (ℓ' : glFunctionals (ψ.scale (-1)) r τ)
    (Φ ΦD : GodementJacquet.MatrixTestFunction r F)
    (φ φD : SchwartzBruhat (Fin (r + 1) → F))
    (χ χD : Quasicharacter F)
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν) :
    let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
      (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
    ∃ (Lq Lh LqD LhD : ℤ) (N : ℕ)
      (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
      AdjacentRankShellLowerBounds F W.val.val Φ φ Lq Lh ∧
      AdjacentRankShellLowerBounds F WD.val.val ΦD φD LqD LhD ∧
      ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
          (glModelRepresentation (ψ.scale (-1)) r τ ℓ'),
          ∀ (m : ℤ) (s : ℂ),
            AdjacentRankShellConvolutionAt F ψ W.val
              (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
              Φ φ χ ν Lq Lh
              (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
              (fun i => (f i).val) m s ∧
            AdjacentRankShellConvolutionAt F (ψ.scale (-1)) WD.val
              (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val
              ΦD φD χD ν LqD LhD
              (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
              (fun i => GodementJacquet.coefficientIota (f i).val) m s := by
  dsimp only
  let σD := inverseTransposePullback σ
  let ℓD := functionalsCongr (standardCharacter_scale_neg_one ψ r).symm
    (dualFunctional ψ σ ℓ)
  let WD := inverseCoefficientAsScaledStandard F ψ σD
    (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
  have hσD : IsSmooth σD :=
    isSmooth_comp (inverseTranspose (r + 1) F).toMonoidHom
      (continuous_inverseTranspose (r + 1) F) hσ
  obtain ⟨Lq, hLq⟩ := exists_whittakerRow_determinantOrder_lowerBound F ψ σ hσ ℓ W φ
  obtain ⟨Lh, hLh⟩ := exists_matrixTest_determinantOrder_lowerBound F Φ
  obtain ⟨LqD, hLqD⟩ := exists_whittakerRow_determinantOrder_lowerBound
    F (ψ.scale (-1)) σD hσD ℓD WD φD
  obtain ⟨LhD, hLhD⟩ := exists_matrixTest_determinantOrder_lowerBound F ΦD
  obtain ⟨N, B, hB⟩ := adjacentRankInnerSlice_matchedFiniteSeparation
    F (ψ.scale (-1)) τ hτ ℓ' Φ ΦD χ χD
  refine ⟨Lq, Lh, LqD, LhD, N, B, ⟨hLq, hLh⟩, ⟨hLqD, hLhD⟩, fun W' => ?_⟩
  obtain ⟨f, hf⟩ := hB W'
  have hfc (i : Fin N) : Continuous (f i).val :=
    (GodementJacquet.isLocallyConstant_biSmoothMatrixCoefficients _ (f i)).continuous
  have hfo := adjacentRankShell_finiteConvolution_of_innerSeparation
    F ψ σ hσ ℓ W (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
    (glModelFunction_continuous (ψ.scale (-1)) r τ hτ.1 ℓ' W')
    Φ φ χ ν hν Lq Lh hLq hLh
    (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
    (fun i => glModelFunction_continuous (ψ.scale (-1)) r τ hτ.1 ℓ' (B i))
    (fun i => (f i).val) hfc (fun j s g => (hf j s g).2.2.2.1)
  have hdc (Z : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule) :
      Continuous (dualModelLinearMap (ψ.scale (-1)) τ ℓ' Z).val.val :=
    (glModelFunction_continuous (ψ.scale (-1)) r τ hτ.1 ℓ' Z).comp
      (continuous_const.mul (continuous_inverseTranspose (r + 1) F))
  have hfd := adjacentRankShell_finiteConvolution_of_innerSeparation
    F (ψ.scale (-1)) σD hσD ℓD WD
    (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val (hdc W')
    ΦD φD χD ν hν LqD LhD hLqD hLhD
    (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
    (fun i => hdc (B i))
    (fun i => GodementJacquet.coefficientIota (f i).val)
    (fun i => (hfc i).comp (continuous_inverseTranspose (r + 1) F))
    (fun j s g => (hf j s g).2.2.2.2)
  exact ⟨f, fun m s => ⟨hfo m s, hfd m s⟩⟩

end Langlands.AllField.RankinSelberg.Padic
