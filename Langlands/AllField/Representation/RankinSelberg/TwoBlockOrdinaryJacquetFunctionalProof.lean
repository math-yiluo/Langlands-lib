import Langlands.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationNonvanishing
import Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement
/-!
# Proof of the ordinary two-block Jacquet functional realization

Proof of `Langlands.AllField.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement`.
-/

noncomputable section

open MeasureTheory

namespace Langlands.AllField.RankinSelberg.TwoBlockOrdinaryJacquet
open Langlands.RankinSelberg.TwoBlockOrdinaryJacquet hiding ordinaryJacquetFunctional ordinaryJacquetFunctional_apply ordinaryJacquetFunctional_inducedRep ordinaryJacquetFunctional_mem ordinaryJacquetFunctional_ne_zero
open Langlands.AllField.RankinSelberg.TwoBlockOrdinaryJacquet
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos character_eq_one_mem_nhds compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_deformed_section_jacquetFunction_one_ne_zero exists_oppositeParabolic_mul exists_section_jacquetFunction_one_ne_zero exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm isSmooth_twoBlockDeformedBlocks jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation

universe uF uW

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable [MeasurableSpace F]
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ψ : UnitaryAdditiveCharacter F)
variable (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
variable (ell : ∀ i, W i →ₗ[ℂ] ℂ)

/-- JPSS (4.6.2) at the identity, `f ↦ J(f)(1)`, as a linear functional on all sections,
when the integrand of every section is absolutely integrable at the identity. -/
def ordinaryJacquetFunctional
    (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    (hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell μ f 1) :
    Sections F h σ →ₗ[ℂ] ℂ where
  toFun f := jacquetFunction ψ ell μ f 1
  map_add' f f' := jacquetFunction_add ψ ell μ (hint f) (hint f')
  map_smul' c f := jacquetFunction_smul ψ ell μ c f 1

theorem ordinaryJacquetFunctional_apply
    (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    (hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell μ f 1) (f : Sections F h σ) :
    ordinaryJacquetFunctional F h ψ σ ell μ hint f = jacquetFunction ψ ell μ f 1 :=
  rfl

/-- The coefficient `g ↦ J(I(g) f)` of the functional is the ordinary integral `J(f)(g)`. -/
theorem ordinaryJacquetFunctional_inducedRep
    (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
    (hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell μ f 1)
    (g : GeneralLinear (t + 1) F) (f : Sections F h σ) :
    ordinaryJacquetFunctional F h ψ σ ell μ hint (inducedRep F h σ g f) =
      jacquetFunction ψ ell μ f g := by
  rw [ordinaryJacquetFunctional_apply, jacquetFunction_inducedRep, one_mul]

/-- For block functionals equivariant for the inverse standard characters, the functional is
equivariant for the inverse standard character of `GL_(t+1)`. -/
theorem ordinaryJacquetFunctional_mem [MeasurableAdd₂ F] [MeasurableMul F]
    (hell : ∀ i, ell i ∈ glInverseFunctionals ψ (m i) (σ i)) :
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure]
      (hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell μ f 1),
      ordinaryJacquetFunctional F h ψ σ ell μ hint ∈ glInverseFunctionals ψ t (inducedRep F h σ) := by
  intro _ μ _ hint n f
  exact jacquetFunction_inducedRep_upperUnipotent F h σ ψ ell hell μ n f

/-- For smooth blocks and nonzero block functionals, the functional is nonzero. -/
theorem ordinaryJacquetFunctional_ne_zero
    (hσ : ∀ i, IsSmooth (σ i))
    (hell : ∀ i, ell i ≠ 0) :
    ∀ [BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [μ.IsAddHaarMeasure]
      (hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell μ f 1),
      ordinaryJacquetFunctional F h ψ σ ell μ hint ≠ 0 := by
  intro _ μ _ hint h0
  obtain ⟨f, -, hf⟩ := exists_section_jacquetFunction_one_ne_zero F h ψ σ hσ ell hell μ
  apply hf
  rw [← ordinaryJacquetFunctional_apply F h ψ σ ell μ hint, h0, LinearMap.zero_apply]

end Langlands.AllField.RankinSelberg.TwoBlockOrdinaryJacquet

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockOrdinaryJacquetFunctionalStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val twoBlockOrdinaryJacquetFunctional
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos character_eq_one_mem_nhds compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_deformed_section_jacquetFunction_one_ne_zero exists_oppositeParabolic_mul exists_section_jacquetFunction_one_ne_zero exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm isSmooth_twoBlockDeformedBlocks jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockOrdinaryJacquet hiding ordinaryJacquetFunctional ordinaryJacquetFunctional_apply ordinaryJacquetFunctional_inducedRep ordinaryJacquetFunctional_mem ordinaryJacquetFunctional_ne_zero
open Langlands.AllField.RankinSelberg.TwoBlockOrdinaryJacquet

universe uF uW

/-- **JPSS 1983, Section (4.6).** For `u` above the ordinary convergence bound, the
ordinary two-block Jacquet integrals are the coefficients of one nonzero
inverse-character Whittaker functional on the actual lower induction. -/
theorem twoBlockOrdinaryJacquetFunctional :
    TwoBlockOrdinaryJacquetFunctionalStatement.{uF, uW} := by
  intro F _ _ _ _ ψ ν t m h W _ _ τ hτ ell hell
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : SecondCountableTopology F := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  have : BorelSpace F := ⟨rfl⟩
  have : BorelSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    inferInstanceAs (BorelSpace (Fin (m 0 + 1) → Fin (m 1 + 1) → F))
  obtain ⟨C, hC⟩ := twoBlockJacquetConvergence F ψ ν t m h τ hτ ell hell
  refine ⟨C, fun u hu => ⟨hC u hu, ?_⟩⟩
  let σ := twoBlockOppositeTwistBlocks F m τ u
  let ell' : ∀ i, W i →ₗ[ℂ] ℂ := fun i => (ell i).val
  let μ := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
  have hint : ∀ f : Sections F h σ, IsAbsIntegrableAt ψ ell' μ f 1 := fun f => hC u hu f 1
  have hmem : ∀ i, ell' i ∈ glInverseFunctionals ψ (m i) (σ i) :=
    fun i => (twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)).property
  have hsmooth : ∀ i, IsSmooth (σ i) :=
    fun i => ((twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).mpr (hτ i)).1.1
  refine ⟨⟨ordinaryJacquetFunctional F h ψ σ ell' μ hint,
    ordinaryJacquetFunctional_mem F h ψ σ ell' hmem μ hint⟩,
    ordinaryJacquetFunctional_ne_zero F h ψ σ ell' hsmooth hell μ hint,
    fun f g => ordinaryJacquetFunctional_inducedRep F h ψ σ ell' μ hint g f⟩

end Langlands.AllField.RankinSelberg
