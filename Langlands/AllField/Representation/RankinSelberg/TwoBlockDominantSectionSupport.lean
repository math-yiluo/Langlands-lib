import Langlands.Representation.RankinSelberg.TwoBlockDominantSectionSupport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceCoordinates
/-! # Internal block-root support for actual induced sections -/

noncomputable section

open scoped BigOperators

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantSectionSupport
open Langlands.RankinSelberg.TwoBlockDominantSectionSupport hiding IsSectionTorusRootBounded exists_blockTensor_rootBounded exists_integral_blockTensor_rootBounded exists_section_torus_rootBounded sectionSupportLocalField sectionSupportTopology sectionSupportValuativeRel
open Langlands.AllField.RankinSelberg.TwoBlockDominantSectionSupport
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding determinantNorm_torus determinantNorm_torus_bounds diagonalDensity diagonalDensity_le exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_section_growth exists_standard_functional_growth instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 isEntryBounded_torus normalizedAbs_uniformizer_zpow torusLevi torusLevi_embedding torusLevi_entryBounded torusLevi_inv_halfModulus_le torusLevi_rotated_twist
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice

universe uF uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

private theorem rootBounded_mono {n L L' : ℕ} {lam : Fin (n + 1) → ℤ}
    (h : RootBounded L lam) (hL : L ≤ L') : RootBounded L' lam := by
  intro i
  exact (h i).trans (add_le_add_right (Int.ofNat_le.mpr hL) _)

/-- Every tensor contraction has one internal root bound in both blocks,
uniformly in the block diagonal exponents and right integral factors. -/
theorem exists_blockTensor_rootBounded
    (ψ : UnitaryAdditiveCharacter F)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsSmooth (τ i)) (ell : ∀ i, glFunctionals ψ (m i) (τ i))
    (w : PiTensorProduct ℂ W) :
    ∃ L : ℕ, ∀ (lam : ∀ i, Fin (m i + 1) → ℤ)
      (c : (succBlockShape m h).Levi F),
      (∀ i, c i ∈ integralOpen F (m i)) →
      tensorContraction (fun i => (ell i).val)
        ((succBlockShape m h).blockTensor τ
          (fun i => Iwasawa.torus
            (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) (lam i) * c i)
          w) ≠ 0 →
      ∀ i, RootBounded L (lam i) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    choose L hL using fun i => exists_coefficient_rootBounded F ψ (τ i) (hτ i) (ell i)
      (modelMap (τ i) (ell i) (v i))
    refine ⟨Finset.univ.sup L, fun lam c hc hne i => ?_⟩
    have hprod : (∏ i, (ell i).val (τ i (Iwasawa.torus
        (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) (lam i) * c i)
        (v i))) ≠ 0 := by
      intro hz
      apply hne
      rw [map_smul, map_smul, BlockShape.blockTensor_tprod, tensorContraction_tprod, hz,
        smul_zero]
    have hi := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
    exact rootBounded_mono (hL i (lam i) (c i) (hc i) hi)
      (Finset.le_sup (Finset.mem_univ i))
  | add w₁ w₂ h₁ h₂ =>
    obtain ⟨L₁, hL₁⟩ := h₁
    obtain ⟨L₂, hL₂⟩ := h₂
    refine ⟨max L₁ L₂, fun lam c hc hne i => ?_⟩
    by_cases hne₁ : tensorContraction (fun i => (ell i).val)
        ((succBlockShape m h).blockTensor τ
          (fun i => Iwasawa.torus
            (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) (lam i) * c i)
          w₁) = 0
    · have hne₂ : tensorContraction (fun i => (ell i).val)
          ((succBlockShape m h).blockTensor τ
            (fun i => Iwasawa.torus
              (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) (lam i) * c i)
            w₂) ≠ 0 := by
        intro hz
        apply hne
        rw [map_add, map_add, hne₁, hz, add_zero]
      exact rootBounded_mono (hL₂ lam c hc hne₂ i) (le_max_right _ _)
    · exact rootBounded_mono (hL₁ lam c hc hne₁ i) (le_max_left _ _)

/-- Finitely many section values on the integral subgroup share one root bound. -/
theorem exists_integral_blockTensor_rootBounded
    (ψ : UnitaryAdditiveCharacter F)
    (τ σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsSmooth (τ i)) (ell : ∀ i, glFunctionals ψ (m i) (τ i))
    (f : Sections F h σ) :
    ∃ L : ℕ, ∀ (c : GeneralLinear (t + 1) F), c ∈ integralOpen F t →
      ∀ (lam : ∀ i, Fin (m i + 1) → ℤ)
        (d : (succBlockShape m h).Levi F),
        (∀ i, d i ∈ integralOpen F (m i)) →
        tensorContraction (fun i => (ell i).val)
          ((succBlockShape m h).blockTensor τ
            (fun i => Iwasawa.torus
              (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) (lam i) * d i)
            (sectionEval F h σ f c)) ≠ 0 →
        ∀ i, RootBounded L (lam i) := by
  classical
  have hfin := finite_image_sectionEval_integralOpen F h σ f
  choose Lw hLw using fun w => exists_blockTensor_rootBounded F h ψ τ hτ ell w
  refine ⟨hfin.toFinset.sup Lw, fun c hc lam d hd hne i => ?_⟩
  have hw : sectionEval F h σ f c ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨c, hc, rfl⟩
  exact rootBounded_mono (hLw _ lam d hd hne i) (Finset.le_sup hw)

/-- A uniform internal block-root bound for nonzero values of an actual
oppositely twisted scalar section on the original torus times the integral subgroup. -/
def IsSectionTorusRootBounded
    (ψ : UnitaryAdditiveCharacter F)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) (u : ℝ)
    (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)) (L : ℕ) : Prop :=
  ∀ (lam : Fin (t + 1) → ℤ) (c : GeneralLinear (t + 1) F),
    c ∈ integralOpen F t →
    scalarSection (fun i => (ell i).val) f
      (Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * c)
      1 ≠ 0 →
    ∀ i, RootBounded L (fun a => lam ((succBlockShape m h).index i a))

/-- Every actual smooth block section admits a uniform internal root bound. -/
theorem exists_section_torus_rootBounded
    (ψ : UnitaryAdditiveCharacter F)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsSmooth (τ i)) (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i)) (u : ℝ)
    (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)) :
    ∃ L, IsSectionTorusRootBounded F h ψ τ ell u f L := by
  let ellD : ∀ i, glFunctionals (ψ.scale (-1)) (m i) (τ i) :=
    fun i => functionalsCongr (standardCharacter_scale_neg_one ψ (m i)).symm (ell i)
  obtain ⟨L, hL⟩ := exists_integral_blockTensor_rootBounded F h (ψ.scale (-1)) τ
    (twoBlockOppositeTwistBlocks F m τ u) hτ ellD f
  refine ⟨L, fun lam c hc hne => ?_⟩
  apply hL c hc (fun i a => lam ((succBlockShape m h).index i a)) 1
    (fun i => (integralOpen F (m i)).one_mem)
  intro hz
  apply hne
  have hcov := scalarSection_covariant (fun i => (ell i).val) f
    ((succBlockShape m h).oppositeLeviInParabolic F (torusLevi F h lam))
    ((succBlockShape m h).oppositeLeviProjection_section F (torusLevi F h lam)) c 1
  rw [BlockShape.oppositeLeviInParabolic_val, one_mul, torusLevi_embedding] at hcov
  rw [hcov, scalarSection_def,
    tensorContraction_blockTensor_twist F h τ u (fun i => (ell i).val)]
  have hz' : tensorContraction (fun i => (ell i).val)
      ((succBlockShape m h).blockTensor τ (torusLevi F h lam)
        (sectionEval F h (twoBlockOppositeTwistBlocks F m τ u) f c)) = 0 := by
    unfold Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice.torusLevi
    simpa only [Pi.one_apply, mul_one, ellD, functionalsCongr] using hz
  rw [hz', mul_zero, mul_zero]

end Langlands.AllField.RankinSelberg.TwoBlockDominantSectionSupport
