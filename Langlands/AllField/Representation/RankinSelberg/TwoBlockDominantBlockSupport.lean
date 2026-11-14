import Langlands.Representation.RankinSelberg.TwoBlockDominantBlockSupport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceSupport
import Langlands.AllField.Representation.RankinSelberg.UnequalRankIwasawaSupportProof
import Langlands.AllField.Representation.Whittaker.TwoBlockJacquetCovarianceProof
/-! # Uniform rectangular support in a leading diagonal block -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg.TwoBlockDominantRectangular hiding IsBlockSumRectangularSupport blockSum_mem_integralOpen exists_blockSum_rectangular_support exists_coefficient_blockSum_rootBounded normalizedAbs_ratios_of_rootBounded twoBlockDominantBlockSupportLocalInstance1
open Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement determinantComplexPower_upperUnipotent diagonal_abs_bound diagonal_abs_last isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val unequalRankIwasawaSupport
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Whittaker hiding MirabolicUnitTestStatement TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier TwoBlockInducingWhittakerCovarianceStatement TwoBlockJacquetCovarianceStatement exchangedParabolic hasCompactSupport_twoBlockCellRestriction mirabolicUnitTest mul_upperUnipotent_mem_twoBlockCell smoothSimpleRootSupport swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockInducingWhittakerCovariance twoBlockJacquetCovariance twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.TwoBlockDeformation hiding blockTensor_twoBlockDeformedBlocks blockZeroNorm blockZeroNorm_mul_integral blockZeroNorm_oppositeParabolic_mul blockZeroNorm_pos compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent determinantNorm_oppositeLeviProjection_of_mem exists_oppositeParabolic_mul exists_uniform_stabilizer flatFunction flatFunction_covariant flatFunction_mul_flatStabilizer flatSection flatSection_zero flatStabilizer flatStabilizer_le_integralOpen inducedRep_mem_compactRadicalSubmodule integralOpen integral_comp_unipotentShift inverseStandardCharacter_eq_prod inverseTranspose_mem_integralOpen isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule isCompact_integralOpen isLocallyConstant_blockZeroNorm isLocallyConstant_oppositeBlockNorm jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule mem_integralOpen mem_oppositeParabolic_of_lower oppositeBlockNorm oppositeBlockNorm_eq oppositeBlockNorm_mul_integral oppositeBlockNorm_oppositeParabolic_mul oppositeBlockNorm_pos radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul sectionEval_mul_flatStabilizer tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockConvergence hiding box boxFieldLocalField boxFieldTopology boxFieldValuativeRel box_eq_pi exists_blockTensor_growth exists_bound_isAbsIntegrable_of_factorization exists_functional_growth exists_integral_growth exists_radical_factorization finite_image_sectionEval_integralOpen integrable_integrand_one measurableSet_box measure_preimage_uniformizer_pow_mul norm_integrand_le norm_inv_leviHalfModulus_le_one normalizedAbs_determinant_eq_one proofFieldBorelSpace proofFieldLocalField proofFieldMeasurableSpace proofFieldTopology proofFieldValuativeRel radicalFieldValuativeRel rectangularMeasure_box residue_pow_rpow_neg tensorContraction_blockTensor_twist uniformizerUnit_isUniformizingElement
open Langlands.AllField.RankinSelberg.TwoBlockConvergence
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_section_growth exists_standard_functional_growth instIsNonarchimedeanLocalFieldCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 isEntryBounded_torus normalizedAbs_uniformizer_zpow
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice

universe uF uV

section Algebra


end Algebra

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

/-- The actual block sum preserves integrality of both matrices and inverses. -/
theorem blockSum_mem_integralOpen {a b : ℕ}
    {A : GeneralLinear (a + 1) F}
    {B : GeneralLinear (b + 1) F}
    (hA : A ∈ integralOpen F a) (hB : B ∈ integralOpen F b) :
    blockSum (A, B) ∈ integralOpen F (a + 1 + b) := by
  have ha := (mem_integralOpen F A).mp hA
  have hb := (mem_integralOpen F B).mp hB
  apply (mem_integralOpen F _).mpr
  constructor
  · intro i l
    induction i using (Fin.addCases (m := a + 1) (n := b + 1)) <;>
      induction l using (Fin.addCases (m := a + 1) (n := b + 1)) <;>
      simp only [blockSum_apply_left, blockSum_apply_right,
        blockSum_apply_left_right, blockSum_apply_right_left]
    · exact ha.1 _ _
    · exact zero_mem _
    · exact zero_mem _
    · exact hb.1 _ _
  · rw [show (blockSum (A, B))⁻¹ = blockSum (A⁻¹, B⁻¹) by
      simpa using (map_inv blockSum (A, B)).symm]
    intro i l
    induction i using (Fin.addCases (m := a + 1) (n := b + 1)) <;>
      induction l using (Fin.addCases (m := a + 1) (n := b + 1)) <;>
      simp only [blockSum_apply_left, blockSum_apply_right,
        blockSum_apply_left_right, blockSum_apply_right_left]
    · exact ha.2 _ _
    · exact zero_mem _
    · exact zero_mem _
    · exact hb.2 _ _

/-- Nonvanishing of a smooth ambient coefficient gives root bounds in
independent Iwasawa decompositions of both actual diagonal blocks. -/
theorem exists_coefficient_blockSum_rootBounded (ψ : UnitaryAdditiveCharacter F)
    {a b : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (a + 1 + (b + 1)) F) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ (a + 1 + b) π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ L : ℕ, ∀ (A : GeneralLinear (a + 1) F)
      (B : GeneralLinear (b + 1) F)
      (c : GeneralLinear (a + 1 + (b + 1)) F),
      c ∈ integralOpen F (a + 1 + b) →
      W.val.val (blockSum (A, B) * c) ≠ 0 →
      ∃ (uA : GeneralLinear (a + 1) F)
        (uB : GeneralLinear (b + 1) F)
        (lam : Fin (a + 1) → ℤ) (mu : Fin (b + 1) → ℤ)
        (kA : GeneralLinear (a + 1) F)
        (kB : GeneralLinear (b + 1) F),
        uA ∈ upperUnipotent (a + 1) F ∧
        uB ∈ upperUnipotent (b + 1) F ∧
        kA ∈ integralOpen F a ∧ kB ∈ integralOpen F b ∧
        A = uA * Iwasawa.torus
          (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * kA ∧
        B = uB * Iwasawa.torus
          (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) mu * kB ∧
        RootBounded L lam ∧ RootBounded L mu := by
  obtain ⟨L, hL⟩ := exists_coefficient_rootBounded F ψ π hπ ell W
  refine ⟨L, fun A B c hc hW => ?_⟩
  have hϖ := uniformizerUnit_isUniformizingElement F
  obtain ⟨uA, huA, lam, kA, hkA, heA⟩ := Iwasawa.exists_iwasawa hϖ A
  obtain ⟨uB, huB, mu, kB, hkB, heB⟩ := Iwasawa.exists_iwasawa hϖ B
  have hkA' : kA ∈ integralOpen F a :=
    (mem_integralOpen F kA).mpr ((Conductor.mem_integralSubgroup _ _ kA).mp hkA)
  have hkB' : kB ∈ integralOpen F b :=
    (mem_integralOpen F kB).mpr ((Conductor.mem_integralSubgroup _ _ kB).mp hkB)
  have hk : blockSum (kA, kB) * c ∈ integralOpen F (a + 1 + b) :=
    (integralOpen F _).mul_mem (blockSum_mem_integralOpen F hkA' hkB') hc
  have hu := blockSum_mem_upperUnipotent ⟨uA, huA⟩ ⟨uB, huB⟩
  have he : blockSum (A, B) * c =
      blockSum (uA, uB) * Iwasawa.torus
        (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
          (Fin.append lam mu) * (blockSum (kA, kB) * c) := by
    rw [← blockSum_torus, heA, heB]
    simp only [← mul_assoc, ← map_mul]
    rfl
  have hW' : W.val.val (Iwasawa.torus
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
        (Fin.append lam mu) * (blockSum (kA, kB) * c)) ≠ 0 := by
    intro hz
    apply hW
    rw [he, mul_assoc, W.val.property ⟨_, hu⟩, hz, mul_zero]
  have hroot := hL (Fin.append (m := a + 1) (n := b + 1) lam mu) _ hk hW'
  exact ⟨uA, uB, lam, mu, kA, kB, huA, huB, hkA', hkB', heA, heB,
    rootBounded_append_left hroot, rootBounded_append_right hroot⟩

/-- Integer adjacent root bounds imply the precise normalized ratio bound. -/
theorem normalizedAbs_ratios_of_rootBounded {a L : ℕ} {lam : Fin (a + 1) → ℤ}
    (h : RootBounded L lam) (i : Fin a) :
    (⟨⟩ : LocalFieldData F).normalizedAbs
      (((Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F) ^ lam i.castSucc) /
        (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F) ^ lam i.succ) :
          Fˣ) : F) ≤
      ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ L := by
  rw [div_eq_mul_inv, ← zpow_sub, normalizedAbs_uniformizer_zpow F]
  have hq : (1 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  calc
    _ ≤ ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ (L : ℤ) :=
      (zpow_le_zpow_iff_right₀ hq).mpr (by have := h i; omega)
    _ = _ := zpow_natCast _ _

/-- A compact rectangle support set uniform in the leading group coordinate,
the other invertible diagonal block and the right integral factor. -/
def IsBlockSumRectangularSupport (ψ : UnitaryAdditiveCharacter F)
    (n j k d : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ
      (GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F) V)
    (ell : glFunctionals ψ (n + (j + k + 1) + 1 + d) π)
    (W : (coefficientModel π ell).toSubmodule)
    (C : Set (Matrix (Fin j) (Fin (n + 1)) F)) : Prop :=
  IsCompact C ∧ ∀ (g : GeneralLinear (n + 1) F)
    (x : Matrix (Fin j) (Fin (n + 1)) F)
    (D : GeneralLinear (d + 1) F)
    (c : GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F),
    c ∈ integralOpen F (n + (j + k + 1) + 1 + d) →
    W.val.val (blockSum (unequalRankMatrix j k g x, D) * c) ≠ 0 →
    x ∈ C

/-- A nonzero smooth ambient coefficient has compact rectangular support in a
leading unequal-rank block, uniformly in the entire other invertible block
and the supplied right integral factor. -/
theorem exists_blockSum_rectangular_support (ψ : UnitaryAdditiveCharacter F)
    (n j k d : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ
      (GeneralLinear (n + (j + k + 1) + 1 + (d + 1)) F) V)
    (hπ : IsSmooth π) (ell : glFunctionals ψ (n + (j + k + 1) + 1 + d) π)
    (W : (coefficientModel π ell).toSubmodule) :
    ∃ C, IsBlockSumRectangularSupport F ψ n j k d π ell W C := by
  obtain ⟨L, hL⟩ := exists_coefficient_blockSum_rootBounded F ψ π hπ ell W
  have hq : (0 : ℝ) < (⟨⟩ : LocalFieldData F).residueCardinality := by
    exact_mod_cast (zero_lt_one.trans (⟨⟩ : LocalFieldData F).residueCardinality_gt_one)
  obtain ⟨C, hC, hsupport⟩ :=
    unequalRankIwasawaSupport F (⟨⟩ : LocalFieldData F) n j k
      (((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^ L) (pow_pos hq L)
  refine ⟨C, hC, fun g x D c hc hW => ?_⟩
  obtain ⟨uA, uB, lam, mu, kA, kB, huA, huB, hkA, hkB, heA, heB, hrA, hrB⟩ :=
    hL (unequalRankMatrix j k g x) D c hc hW
  exact hsupport g x uA
    (fun i => Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F) ^ lam i)
    kA huA ((Conductor.mem_integralSubgroup _ _ kA).mpr ((mem_integralOpen F kA).mp hkA))
    heA (normalizedAbs_ratios_of_rootBounded F hrA)

end Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular
