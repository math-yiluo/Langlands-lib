import Langlands.Representation.RankinSelberg.AdjacentRankModelZetaCoefficient
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankShellConvolution
import Langlands.AllField.Representation.RankinSelberg.AnalyticBridge
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport
import Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
/-! The actual model substitution preceding the finite convolution in JPSS 6.3. -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.QuotientIntegration
open scoped BigOperators

universe uF uV uW

namespace Padic
open Langlands.RankinSelberg.Padic hiding AdjacentRankModelConverges adjacentRankBeforeShearKernel adjacentRankBeforeShearKernel_mk adjacentRankCompact_middleAverage adjacentRankInnerMultiplier adjacentRankInnerMultiplier_mul adjacentRankInnerSliceWeight adjacentRankInnerSliceWeight_mul adjacentRankJointShell adjacentRankJointShellKernel adjacentRankJointShellKernel_mk adjacentRankJointShellKernel_mk_eq_innerSlice adjacentRankModelIntegral adjacentRankModelIntegral_separated_rankInclusion_raw adjacentRankModelIntegral_separated_rankInclusion_weighted adjacentRankModel_corankOneSlice_eq_before adjacentRankSeparatedTest_rho0_rankInclusion adjacentRankShell_shear_fubini compactCoefficientsBorel compactCoefficientsLocalField compactCoefficientsMeasurable compactCoefficientsTopology compactCoefficientsValuativeRel continuous_adjacentRankInnerMultiplier continuous_adjacentRankInnerSliceWeight continuous_adjacentRankJointShellKernel exists_adjacentRankInner_subgroup exists_matrixTest_determinantOrder_lowerBound exists_whittakerRow_determinantOrder_lowerBound hasCompactSupport_adjacentRankInnerSliceWeight hasCompactSupport_adjacentRankJointShellKernel hasCompactSupport_equalRankSlice innerSliceFieldTopology innerSliceGroupBorel innerSliceGroupMeasurable innerSliceLocalField innerSliceValuativeRel instBorelSpaceCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instT2SpaceCarrier instTopologicalSpaceCarrier instTotallyDisconnectedSpaceCarrier instValuativeRelCarrier integrable_adjacentRankInnerSliceWeight_mul integrable_adjacentRankJointShellKernel integrable_equalRankSlice integral_eq_sum_determinantSlices isClopen_adjacentRankJointShell jointShellFieldT2 jointShellFieldTopology jointShellGroupBorelSpace jointShellGroupMeasurableSpace jointShellGroupSecondCountable jointShellGroupSigmaCompact jointShellLocalField jointShellQuotientBorelSpace jointShellQuotientMeasurableSpace jointShellQuotientT2 jointShellValuativeRel modelZetaFieldBorel modelZetaFieldMeasurable modelZetaFieldT2 modelZetaFieldTopology modelZetaFieldTotallyDisconnected modelZetaGroupBorel modelZetaGroupMeasurable modelZetaLocalField modelZetaValuativeRel quotientShearFieldT2 quotientShearFieldTopology quotientShearGroupBorel quotientShearGroupMeasurable quotientShearGroupSecondCountable quotientShearGroupSigmaCompact quotientShearLocalField quotientShearQuotientBorel quotientShearQuotientLocallyCompact quotientShearQuotientMeasurable quotientShearQuotientSecondCountable quotientShearUnipotentBorel quotientShearUnipotentMeasurable quotientShearValuativeRel shellConvolutionFieldTopology shellConvolutionLocalField shellConvolutionQuotientBorel shellConvolutionQuotientMeasurable shellConvolutionValuativeRel
open Langlands.AllField.RankinSelberg.Padic
open Langlands.RankinSelberg hiding AdjacentRankModelConvergenceStatement AdjacentRankModelConverges EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement WhittakerRowSliceCompactSupportStatement ZeroRowLastRowCutoffStatement adjacentRankModelConvergence adjacentRankModelConvergenceProofLocalInstance1 adjacentRankModelConvergenceProofLocalInstance2 adjacentRankModelConvergenceProofLocalInstance3 adjacentRankModelConvergenceProofLocalInstance4 adjacentRankModelConvergenceProofLocalInstance5 adjacentRankModelConvergenceProofLocalInstance6 adjacentRankModelConvergenceProofLocalInstance7 adjacentRankModelConvergenceProofLocalInstance8 adjacentRankModelConvergenceProofLocalInstance9 adjacentRankModelConverges_tmul_of_isSmooth adjacentRankModelIntegral adjacentRankModelIntegrand adjacentRankPure_hasCompactSupport continuous_adjacentRankKernelMatrix continuous_adjacentRank_determinantWeight continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_adjacentRank_lastColumn_bound exists_iwasawa_diagonal_le_of_simpleRoot exists_schwartzBruhat_row_bound generalLinearDeterminantSlice hasCompactSupport_matrixSlice iUnion_determinantSlice isClopen_determinantSlice isClopen_generalLinearDeterminantSlice isClosed_determinantSlice isCompact_normalizedAbs_annulus_units isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice lastRowCompactOrbit matrixSliceTest matrixSliceTest_apply measurableSet_determinantSlice mem_determinantSlice mem_generalLinearDeterminantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_det_of_mem_generalLinearDeterminantSlice normalizedAbs_det_of_mem_integralSubgroup normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable whittakerRowSliceCompactSupport zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance modelZetaFieldT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance modelZetaFieldTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance modelZetaFieldMeasurable : MeasurableSpace F := borel _
local instance modelZetaFieldBorel : BorelSpace F := ⟨rfl⟩
local instance modelZetaGroupMeasurable (r : ℕ) : MeasurableSpace
    (Langlands.GeneralLinear (r + 1) F) := borel _
local instance modelZetaGroupBorel (r : ℕ) : BorelSpace
    (Langlands.GeneralLinear (r + 1) F) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

theorem adjacentRankInnerMultiplier_mul {r : ℕ}
    (χ : Quasicharacter F) (s : ℂ)
    (h g : Langlands.GeneralLinear (r + 1) F) :
    adjacentRankInnerMultiplier F χ s (h * g) =
      adjacentRankInnerMultiplier F χ s h * adjacentRankInnerMultiplier F χ s g := by
  simp only [adjacentRankInnerMultiplier, map_mul, Units.val_mul, determinantWeight_mul]
  ring

/-- The proved elementary Fourier covariance evaluates the separated test
at precisely the square block `h g` and the last row of `h⁻¹`. -/
theorem adjacentRankSeparatedTest_rho0_rankInclusion
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (g h : Langlands.GeneralLinear (r + 1) F) :
    rectangularRho0 ψ μ (r + 1) hself (GeneralLinear.rankInclusion 1 g)
        (adjacentRankSeparatedTest Φ φ) (adjacentRankKernelMatrix h) =
      Φ (h * g).val * φ (lastRow h⁻¹) := by
  rw [(partialFourierCovariance ψ μ (r + 1) hself).1,
    rectangularTranslate_apply, adjacentRankKernelMatrix,
    rectangularJoin_mul_rankInclusion, adjacentRankSeparatedTest_join]
  have he := funext (inverseTranspose_mulVec_adjacentRankEpsilon h)
  rw [he]
  rfl

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Direct substitution of a separated pure tensor into the literal model.
No Whittaker image or spanning assertion is assumed. -/
theorem adjacentRankModelIntegral_separated_rankInclusion_raw
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (r + 1) F) :
    adjacentRankModelIntegral F ψ μ hself σ ℓ χ
        (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) (GeneralLinear.rankInclusion 1 g) =
      (χ (GeneralLinear.determinant g) : ℂ) *
        determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
        ∫ h, Φ (h * g).val * φ (lastRow h⁻¹) * W.val.val h⁻¹ *
          adjacentRankInnerMultiplier F χ ((r : ℂ) / 2) h
            ∂generalLinearHaar F r := by
  unfold adjacentRankModelIntegral
  rw [RankinSelberg.adjacentRankModelIntegral_tmul]
  have hdet : GeneralLinear.determinant (GeneralLinear.rankInclusion 1 g) =
      GeneralLinear.determinant g :=
    Units.ext (det_rankInclusion 1 g)
  have hw : determinantWeight abv (GeneralLinear.rankInclusion 1 g)
      (((r + 1 : ℕ) : ℂ) / 2) =
      determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) := by
    simp only [determinantWeight, det_rankInclusion]
  rw [hdet, hw]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro h
  dsimp only
  rw [adjacentRankSeparatedTest_rho0_rankInclusion F]
  change (Φ _ * φ _ * W.val.val _ *
    (χ (GeneralLinear.determinant h) : ℂ) *
      determinantWeight abv h ((r : ℂ) / 2)) = _
  unfold adjacentRankInnerMultiplier
  ring

/-- Right substitution in the same GL Haar measure and cancellation of the
two half-weights give the kernel used in the shell convolution. -/
theorem adjacentRankModelIntegral_separated_rankInclusion_weighted
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (r + 1) F) (s : ℂ) :
    adjacentRankModelIntegral F ψ μ hself σ ℓ χ
        (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) (GeneralLinear.rankInclusion 1 g) *
        determinantWeight abv g (s - 1 / 2) =
      determinantWeight abv g s *
        ∫ h, Φ h.val * φ (lastRow (g * h⁻¹)) * W.val.val (g * h⁻¹) *
          adjacentRankInnerMultiplier F χ ((r : ℂ) / 2) h
            ∂generalLinearHaar F r := by
  let a := adjacentRankInnerMultiplier F (r := r) χ ((r : ℂ) / 2)
  let orig := fun h : Langlands.GeneralLinear (r + 1) F =>
    Φ (h * g).val * φ (lastRow h⁻¹) * W.val.val h⁻¹ * a h
  let after := fun h : Langlands.GeneralLinear (r + 1) F =>
    Φ h.val * φ (lastRow (g * h⁻¹)) * W.val.val (g * h⁻¹) * a h
  have he : ∀ h, after (h * g) = a g * orig h := by
    intro h
    dsimp only [after, orig, a]
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul,
      adjacentRankInnerMultiplier_mul]
    ring
  have hi : (∫ h, after h ∂generalLinearHaar F r) =
      a g * ∫ h, orig h ∂generalLinearHaar F r := by
    rw [← integral_mul_right_eq_self after g]
    simp_rw [he]
    exact integral_const_mul _ _
  have hw : (χ (GeneralLinear.determinant g) : ℂ) *
      determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
      determinantWeight abv g (s - 1 / 2) =
        determinantWeight abv g s * a g := by
    dsimp only [a, adjacentRankInnerMultiplier]
    rw [mul_assoc, ← determinantWeight_exponent_add, mul_left_comm,
      ← determinantWeight_exponent_add]
    congr 2
    push_cast
    ring
  rw [adjacentRankModelIntegral_separated_rankInclusion_raw F]
  change ((χ (GeneralLinear.determinant g) : ℂ) *
    determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
      (∫ h, orig h ∂generalLinearHaar F r)) *
        determinantWeight abv g (s - 1 / 2) =
      determinantWeight abv g s * ∫ h, after h ∂generalLinearHaar F r
  rw [hi]
  calc
    _ = ((χ (GeneralLinear.determinant g) : ℂ) *
        determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
        determinantWeight abv g (s - 1 / 2)) *
          (∫ h, orig h ∂generalLinearHaar F r) := by ring
    _ = _ := by rw [hw]; ring

/-- A Whittaker function realized by this separated model has exactly the
before-shear kernel on each determinant slice. Realization is explicit data. -/
theorem adjacentRankModel_corankOneSlice_eq_before
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F)
    (Φ : GodementJacquet.MatrixTestFunction r F)
    (φ : SchwartzBruhat (Fin (r + 1) → F))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (U : WhittakerFunctions ψ (r + 1))
    (hU : ∀ g, U.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g)
    (W' : InverseWhittakerFunctions ψ r) (m : ℤ)
    (q : LeftUnipotentQuotient r F) :
    (determinantSlice (⟨⟩ : LocalFieldData F) r m).indicator
        (corankOneIntegrand ψ abv U W' 0) q =
      ∫ h, adjacentRankBeforeShearKernel F ψ W.val W' Φ φ
        (adjacentRankInnerMultiplier F χ ((r : ℂ) / 2)) m (q, h)
          ∂generalLinearHaar F r := by
  classical
  induction q using Quotient.inductionOn with
  | h g =>
    by_cases hg : (⟨⟩ : LocalFieldData F).ord
        (GeneralLinear.determinant g : F) = m
    · rw [Set.indicator_of_mem (show Quotient.mk _ g ∈
        determinantSlice (⟨⟩ : LocalFieldData F) r m from hg),
        corankOneIntegrand_mk, hU]
      have hw := adjacentRankModelIntegral_separated_rankInclusion_weighted
        F ψ μ hself σ ℓ χ Φ φ W g 0
      simp only [determinantWeight_zero, one_mul] at hw
      calc
        _ = (adjacentRankModelIntegral F ψ μ hself σ ℓ χ
              (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) (GeneralLinear.rankInclusion 1 g) *
              determinantWeight abv g (0 - 1 / 2)) * W'.val g := by ring
        _ = (∫ h, Φ h.val * φ (lastRow (g * h⁻¹)) * W.val.val (g * h⁻¹) *
              adjacentRankInnerMultiplier F χ ((r : ℂ) / 2) h
                ∂generalLinearHaar F r) * W'.val g := by rw [hw]
        _ = ∫ h, (Φ h.val * φ (lastRow (g * h⁻¹)) * W.val.val (g * h⁻¹) *
              adjacentRankInnerMultiplier F χ ((r : ℂ) / 2) h) * W'.val g
                ∂generalLinearHaar F r := (integral_mul_const _ _).symm
        _ = _ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun h => by
            dsimp only
            rw [adjacentRankBeforeShearKernel_mk, ite_eq_left hg]
            ring
    · rw [Set.indicator_of_notMem (show Quotient.mk _ g ∉
        determinantSlice (⟨⟩ : LocalFieldData F) r m from hg)]
      simp only [adjacentRankBeforeShearKernel_mk, ite_eq_right hg, integral_zero]

end Padic
end Langlands.AllField.RankinSelberg
