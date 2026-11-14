import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceSupport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceGrowth
import Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportProof
/-! # Integer simple-root support for fixed-slice convergence -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal ENNReal

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_section_growth exists_standard_functional_growth instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 isEntryBounded_torus normalizedAbs_uniformizer_zpow
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- Canonical torus powers have the normalized residue-cardinality absolute value. -/
theorem normalizedAbs_uniformizer_zpow (z : ℤ) :
    (⟨⟩ : LocalFieldData F).normalizedAbs
      (((Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) ^ z :
        Fˣ) : F) =
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (-z) := by
  set T := (⟨⟩ : LocalFieldData F)
  rw [T.normalizedAbs_of_ne_zero (Units.ne_zero _),
    Units.val_zpow_eq_zpow_val, Langlands.LocalFactor.LocalAbelian.uniformizerUnit_coe,
    T.ord_zpow, T.ord_uniformizer, mul_one]

/-- One integer simple-root bound works for every diagonal and compact factor of
an actual smooth coefficient-image vector. -/
theorem exists_coefficient_rootBounded (ψ : UnitaryAdditiveCharacter F)
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (n + 1) F) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ n π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ L : ℕ, ∀ (lam : Fin (n + 1) → ℤ) (k : GeneralLinear (n + 1) F),
      k ∈ integralOpen F n →
      W.val.val (Iwasawa.torus
        (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * k) ≠ 0 →
      RootBounded L lam := by
  set T := (⟨⟩ : LocalFieldData F)
  obtain ⟨R, _, hR⟩ := smoothSimpleRootSupport F T n ψ V π hπ ell W
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨L, hL⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop R).exists
  refine ⟨L, fun lam k hk hne i => ?_⟩
  have hk' : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer n :=
    (Conductor.mem_integralSubgroup _ n k).2 ((mem_integralOpen F k).1 hk)
  have hs := hR
    (fun j => Langlands.LocalFactor.LocalAbelian.uniformizerUnit T ^ lam j) k hk' hne i
  rw [div_eq_mul_inv, ← zpow_sub, normalizedAbs_uniformizer_zpow F] at hs
  have hexp : (T.residueCardinality : ℝ) ^ (-(lam i.castSucc - lam i.succ)) ≤
      (T.residueCardinality : ℝ) ^ (L : ℤ) := by
    simpa only [zpow_natCast] using hs.trans hL.le
  have := (zpow_le_zpow_iff_right₀ hq).mp hexp
  omega

end Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
