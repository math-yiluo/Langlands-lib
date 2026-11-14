import Langlands.Representation.RankinSelberg.TwoBlockFixedSliceAnalysis
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData
/-! # Continuity of the actual first-unfolding averages

Internal analytic helpers for the fixed-slice unfolding of JPSS Section 4.6.
The open right stabilizer of a smooth section makes its entire raw Jacquet
integrand, as a function of the rectangular variable, locally constant in the
group variable. Integrating therefore preserves local constancy without a
parameter-dependent domination argument.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AllField.RankinSelberg.TwoBlockUnfolding
open Langlands.RankinSelberg.TwoBlockUnfolding hiding fiberIntegral_integrand groupIntegrand groupIntegrand_blockUnipotent_mul groupIntegrand_def integrand integrand_continuous integrand_fiberPoint integrand_mk inverseStandardCharacter_blockEmbedding radicalAverage_integrand_mk radicalAverage_norm_integrand_mk radicalAverages_continuous rawIntegrand_isLocallyConstant scalarSection_blockEmbedding_mul scalarSection_blockEmbedding_mul_eq_inverseStandardCharacter
open Langlands.AllField.RankinSelberg.TwoBlockUnfolding
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet hiding integrand
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice radicalAverage radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient hiding determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.QuotientIntegration
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uW

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}

section Raw

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ψ : UnitaryAdditiveCharacter F) (ell : ∀ i, W i →ₗ[ℂ] ℂ)

/-- The whole rectangular integrand is locally constant in the group argument. -/
theorem rawIntegrand_isLocallyConstant (f : Sections F h σ) :
    IsLocallyConstant (fun g => Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand ψ ell f g) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  obtain ⟨K, hK⟩ := f.property
  apply (IsLocallyConstant.iff_exists_open _).2
  intro g
  refine ⟨(fun a => g⁻¹ * a) ⁻¹' (K : Set (GeneralLinear (t + 1) F)),
    K.isOpen.preimage (continuous_const.mul continuous_id), by simp, ?_⟩
  intro a ha
  funext x
  have hfix := congrArg
    (fun v => v.val (upperRadical h F x * g)) (hK ⟨g⁻¹ * a, ha⟩)
  change f.val.val ((upperRadical h F x * g) * (g⁻¹ * a)) =
    f.val.val (upperRadical h F x * g) at hfix
  have heval : sectionEval F h σ f (upperRadical h F x * a) =
      sectionEval F h σ f (upperRadical h F x * g) := by
    simpa only [sectionEval, Induction.eval, mul_assoc, mul_inv_cancel_left] using hfix
  simp only [Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand_apply, heval]

end Raw

section Averages

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ψ : UnitaryAdditiveCharacter F)
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
variable (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ t)
variable (Φ : SchwartzBruhat (Fin (t + 1) → F))

/-- Continuity descends from the actual continuous group integrand. -/
theorem integrand_continuous :
    Continuous Wtest.val → Continuous (integrand ell f Wtest Φ) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  intro hW
  have hs : Continuous (fun g => scalarSection (fun i => (ell i).val) f g 1) := by
    simpa only [scalarSection_one, Function.comp_def] using
      ((Induction.eval_isLocallyConstant _ _ f).comp (tensorContraction (fun i => (ell i).val))).continuous
  have hr : Continuous (lastRow : GeneralLinear (t + 1) F → _) :=
    continuous_pi (fun j => Units.continuous_val.matrix_elem (Fin.last t) j)
  apply (leftQuotient_isOpenQuotientMap (blockUnipotent h F)).isQuotientMap.continuous_iff.mpr
  exact (hW.mul hs).mul (Φ.locallyConstant.continuous.comp hr)

variable [MeasurableSpace F]

/-- Absolute fiber average on a representative, factored into row norms and
an integral of the absolute raw Jacquet integrand. -/
theorem radicalAverage_norm_integrand_mk :
    ∀ [BorelSpace F]
      (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
      [μR.IsAddHaarMeasure] (g : GeneralLinear (t + 1) F),
      radicalAverage F h μR (fun z => (‖integrand ell f Wtest Φ z‖ : ℂ)) (Quotient.mk _ g) =
        (‖Wtest.val g‖ : ℂ) *
          (∫ x, (‖Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x‖ : ℂ) ∂μR) *
          (‖Φ (lastRow g)‖ : ℂ) := by
  intro _ μR _ g
  simp only [radicalAverage_mk, integrand_fiberPoint, norm_mul, Complex.ofReal_mul,
    integral_mul_const, integral_const_mul]

/-- Both the signed and absolute averages are continuous. No convergence
hypothesis is used here; convergence will be supplied separately. -/
theorem radicalAverages_continuous :
    ∀ [BorelSpace F]
      (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
      [μR.IsAddHaarMeasure], Continuous Wtest.val →
      Continuous (radicalAverage F h μR (integrand ell f Wtest Φ)) ∧
      Continuous (radicalAverage F h μR (fun z => (‖integrand ell f Wtest Φ z‖ : ℂ))) := by
  let := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (t + 1)
  intro _ μR _ hW
  have hlc := rawIntegrand_isLocallyConstant ψ (fun i => (ell i).val) f
  have hj : Continuous (jacquetFunction ψ (fun i => (ell i).val) μR f) :=
    (hlc.comp (fun v => ∫ x, v x ∂μR)).continuous
  have ha : Continuous (fun g => ∫ x,
      (‖Langlands.AllField.RankinSelberg.TwoBlockJacquet.integrand ψ (fun i => (ell i).val) f g x‖ : ℂ) ∂μR) :=
    (hlc.comp (fun v => ∫ x, (‖v x‖ : ℂ) ∂μR)).continuous
  have hr : Continuous (fun g : GeneralLinear (t + 1) F => Φ (lastRow g)) :=
    Φ.locallyConstant.continuous.comp
      (continuous_pi (fun j => Units.continuous_val.matrix_elem (Fin.last t) j))
  constructor
  · apply (leftQuotient_isOpenQuotientMap (upperUnipotent (t + 1) F)).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, Pi.mul_def, leftQuotientMap_apply, radicalAverage_integrand_mk] using
      (hW.mul hj).mul hr
  · apply (leftQuotient_isOpenQuotientMap (upperUnipotent (t + 1) F)).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, Pi.mul_def, leftQuotientMap_apply, radicalAverage_norm_integrand_mk] using
      ((Complex.continuous_ofReal.comp hW.norm).mul ha).mul
        (Complex.continuous_ofReal.comp hr.norm)

end Averages

end Langlands.AllField.RankinSelberg.TwoBlockUnfolding
