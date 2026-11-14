import Langlands.Representation.RankinSelberg.TwoBlockDominantJacquetSeries
import Langlands.AllField.Representation.Induction.OppositeProductReversalProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankSliceSupportProof
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData
/-!
# Actual Jacquet coefficient series at the equal-rank boundary

Internal assembly of the published ordinary Jacquet realization, normalized
induction type preservation, quotient integrand and lower-support theorem.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg.DominantRankTransport hiding instBorelSpaceCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier lowerInduced_inverseWhittakerType radicalAverage_eq_equalRankIntegrand unfoldedJacquetSeries unfoldedJacquetSeries_eq
open Langlands.AllField.RankinSelberg.DominantRankTransport
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankSliceSupportStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceSupport exists_schwartzBruhat_row_bound iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbs_determinant_le_of_simpleRoot normalizedAbs_finsetSum_le normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow normalizedProductWhittakerType pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier UnipotentOrbitStatement compactLocalization exchangedParabolic functionalsCongr hasCompactSupport_twoBlockCellRestriction inducedLocalization_of_prerequisites mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentOrbit unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice radicalAverage radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient hiding determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF uV uW

variable (F : Type uF) [Field F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Full inverse-standard type of the actual lower induction, obtained by
reversing all sizes, carriers and representations before using upper type. -/
theorem lowerInduced_inverseWhittakerType [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    IsOfWhittakerType t (inverseStandardCharacter ψ t)
      (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) := by
  obtain ⟨E, -, -⟩ := glOppositeProductReversal F (⟨⟩ : LocalFieldData F)
    (t + 1) (succBlockShape m h) W σ (fun i => (hσ i).1.1)
  have hrev : ∑ i : Fin 2, (m i.rev + 1) = t + 1 :=
    (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
  have hupper := normalizedProductWhittakerType F ψ t 2 (fun i => m i.rev) hrev
    (W := fun i => W i.rev) (fun i => σ i.rev) (fun i => hσ i.rev)
  exact (isOfWhittakerType_standard_iff_inverse ψ _).1 (hupper.of_equiv E.symm)

section Series

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (μR : letI := borel F;
    Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
  [μR.IsAddHaarMeasure]
  (μN : letI := borel (LeftUnipotentQuotient t F);
    Measure (LeftUnipotentQuotient t F))

/-- Determinant-slice integrals of the actual first-unfolding radical average.
The two supplied measures are retained. -/
def unfoldedJacquetSeries (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
    (Wtest : WhittakerFunctions ψ t)
    (Φ : SchwartzBruhat (Fin (t + 1) → F)) : BilateralLaurentSeries :=
  letI : MeasurableSpace F := borel F
  sliceCoefficient (⟨⟩ : LocalFieldData F) μN
    (radicalAverage F h μR (Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest Φ))

/-- The radical average is the actual equal-rank integrand associated to a
functional whose coefficients are the ordinary Jacquet integrals. -/
theorem radicalAverage_eq_equalRankIntegrand
    (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
    (hJ : ∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
      (g : GeneralLinear (t + 1) F),
      J.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ g f) =
        Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μR f g)
    (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
    (Wtest : WhittakerFunctions ψ t)
    (Φ : SchwartzBruhat (Fin (t + 1) → F)) :
    letI : MeasurableSpace F := borel F
    radicalAverage F h μR (Langlands.AllField.RankinSelberg.TwoBlockUnfolding.integrand ell f Wtest Φ) =
      equalRankIntegrand ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
        Wtest (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f).val Φ 0 := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [Langlands.AllField.RankinSelberg.TwoBlockUnfolding.radicalAverage_integrand_mk, equalRankIntegrand_zero_mk]
    change Wtest.val g * Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ
        (fun i => (ell i).val) μR f g * Φ (lastRow g) =
      Wtest.val g * J.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ g f) * Φ (lastRow g)
    rw [hJ]

/-- Identification of the unfolded coefficient series, without a convergence
premise. This is equality of total restricted Bochner integrals. -/
theorem unfoldedJacquetSeries_eq
    (J : glInverseFunctionals ψ t (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ))
    (hJ : ∀ (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
      (g : GeneralLinear (t + 1) F),
      J.val (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ g f) =
        Langlands.AllField.RankinSelberg.TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μR f g)
    (f : Langlands.AllField.RankinSelberg.TwoBlockJacquet.Sections F h σ)
    (Wtest : WhittakerFunctions ψ t)
    (Φ : SchwartzBruhat (Fin (t + 1) → F)) :
    unfoldedJacquetSeries F h ψ σ ell μR μN f Wtest Φ =
      equalRankSliceCoefficient (⟨⟩ : LocalFieldData F) μN ψ
        Wtest (modelMap (Langlands.AllField.RankinSelberg.TwoBlockJacquet.inducedRep F h σ) J f).val Φ := by
  unfold unfoldedJacquetSeries equalRankSliceCoefficient
  rw [radicalAverage_eq_equalRankIntegrand F h ψ σ ell μR J hJ f Wtest Φ]

end Series

section Family

variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
local instance : SecondCountableTopology F := (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (GeneralLinear (t + 1) F) :=
  borel (GeneralLinear (t + 1) F)
local instance : BorelSpace (GeneralLinear (t + 1) F) := ⟨rfl⟩
local instance : MeasurableSpace (upperUnipotent (t + 1) F) :=
  borel (upperUnipotent (t + 1) F)
local instance : BorelSpace (upperUnipotent (t + 1) F) := ⟨rfl⟩
local instance : MeasurableSpace (LeftUnipotentQuotient t F) :=
  borel (LeftUnipotentQuotient t F)
local instance : BorelSpace (LeftUnipotentQuotient t F) := ⟨rfl⟩

end Family

end Langlands.AllField.RankinSelberg.DominantRankTransport
