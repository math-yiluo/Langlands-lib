import Langlands.Representation.RankinSelberg.AdjacentRankQuotientShear
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankJointShell
/-! The actual quotient shear and fixed-shell Fubini step in JPSS Section 6.3. -/

noncomputable section

namespace Langlands.AllField.QuotientIntegration
open Langlands.QuotientIntegration
open Langlands.AllField.QuotientIntegration

open _root_.MeasureTheory

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G)

section Measure



end Measure
end Langlands.AllField.QuotientIntegration

namespace Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankModelIntegral adjacentRankShell_shear_fubini continuous_adjacentRankJointShellKernel exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankJointShellKernel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankJointShellKernel isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelConverges EqualRankAnalyticStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open Langlands.AllField.QuotientIntegration

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance quotientShearFieldT2 : T2Space F :=
  (⟨⟩ : LocalFieldData F).fieldT2
local instance quotientShearGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F) := borel _
local instance quotientShearGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩
local instance quotientShearUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear.upperUnipotent (r + 1) F) := borel _
local instance quotientShearUnipotentBorel (r : ℕ) :
    BorelSpace (GeneralLinear.upperUnipotent (r + 1) F) := ⟨rfl⟩
local instance quotientShearQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F) := borel _
local instance quotientShearQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F) := ⟨rfl⟩
local instance quotientShearGroupSecondCountable (r : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear (r + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology (r + 1)
local instance quotientShearGroupSigmaCompact (r : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (r + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (r + 1)
local instance quotientShearQuotientSecondCountable (r : ℕ) :
    SecondCountableTopology (LeftUnipotentQuotient r F) :=
  TopologicalSpace.Quotient.secondCountableTopology
    (leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (r + 1) F)).isOpenMap
local instance quotientShearQuotientLocallyCompact (r : ℕ) :
    LocallyCompactSpace (LeftUnipotentQuotient r F) :=
  leftQuotient_locallyCompactSpace _

/-- The genuine kernel before the change `g ↦ g h`, defined by inverse shear. -/
def adjacentRankBeforeShearKernel {r : ℕ} (ψ : UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (a : Langlands.GeneralLinear (r + 1) F → ℂ) (m : ℤ) :
    LeftUnipotentQuotient r F × Langlands.GeneralLinear (r + 1) F → ℂ :=
  adjacentRankJointShellKernel F ψ W W' Φ φ a m ∘
    (rightQuotientShear (GeneralLinear.upperUnipotent (r + 1) F)).symm

@[simp] theorem adjacentRankBeforeShearKernel_mk {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (a : Langlands.GeneralLinear (r + 1) F → ℂ) (m : ℤ)
    (g h : Langlands.GeneralLinear (r + 1) F) :
    adjacentRankBeforeShearKernel F ψ W W' Φ φ a m (Quotient.mk _ g, h) =
      if (⟨⟩ : LocalFieldData F).ord (GeneralLinear.determinant g : F) = m
      then W.val (g * h⁻¹) * W'.val g * φ (lastRow (g * h⁻¹)) * Φ h.val * a h
      else 0 := by
  simp only [adjacentRankBeforeShearKernel, Function.comp_apply,
    rightQuotientShear_symm_mk, adjacentRankJointShellKernel_mk, inv_mul_cancel_right]
  rw [map_mul, Units.val_mul,
    (⟨⟩ : LocalFieldData F).ord_mul
      (GeneralLinear.determinant g).ne_zero (GeneralLinear.determinant h⁻¹).ne_zero,
    map_inv, Units.val_inv_eq_inv_val, (⟨⟩ : LocalFieldData F).ord_inv]
  simp only [add_assoc, neg_add_cancel, add_zero]

/-- Absolute convergence of both kernels, both iterated integrals and their
exact equality for every supplied compatible quotient measure. -/
theorem adjacentRankShell_shear_fubini {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r) (hW' : Continuous W'.val)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (a : Langlands.GeneralLinear (r + 1) F → ℂ) (ha : Continuous a) (m : ℤ)
    (ν : Measure (LeftUnipotentQuotient r F))
    (hν : IsCompatible (GeneralLinear.upperUnipotent (r + 1) F)
      (generalLinearHaar F r) (unipotentHaar F r) ν) :
    let η := generalLinearHaar F r
    let before := adjacentRankBeforeShearKernel F ψ W.val W' Φ φ a m
    let after := adjacentRankJointShellKernel F ψ W.val W' Φ φ a m
    Integrable before (ν.prod η) ∧ Integrable after (ν.prod η) ∧
      Integrable (fun q => ∫ h, before (q, h) ∂η) ν ∧
      Integrable (fun q => ∫ h, after (q, h) ∂η) ν ∧
      Integrable (fun h => ∫ q, after (q, h) ∂ν) η ∧
      (∫ q, ∫ h, before (q, h) ∂η ∂ν) = ∫ q, ∫ h, after (q, h) ∂η ∂ν ∧
      (∫ q, ∫ h, after (q, h) ∂η ∂ν) = ∫ h, ∫ q, after (q, h) ∂ν ∂η := by
  dsimp only
  let := hν.regular
  have hi := integrable_adjacentRankJointShellKernel F ψ σ hσ ℓ W W' hW'
    Φ φ a ha m ν (generalLinearHaar F r)
  have hb : Integrable (adjacentRankBeforeShearKernel F ψ W.val W' Φ φ a m)
      (ν.prod (generalLinearHaar F r)) :=
    (integrable_comp_rightQuotientShear_symm_iff _ ν
      (generalLinearHaar F r) hν.right_invariant _).mpr hi
  refine ⟨hb, hi, hb.integral_prod_left, hi.integral_prod_left, hi.integral_prod_right, ?_, ?_⟩
  · rw [← integral_prod _ hb, ← integral_prod _ hi]
    exact integral_comp_rightQuotientShear_symm _ ν
      (generalLinearHaar F r) hν.right_invariant _
  · rw [← integral_prod _ hi, ← integral_prod_symm _ hi]

end Langlands.AllField.RankinSelberg.Padic
