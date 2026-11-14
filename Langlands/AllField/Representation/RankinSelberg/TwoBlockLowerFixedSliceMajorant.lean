import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMajorant
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerCompactFourier
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceCoordinates
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerIntegralRotation
/-! # A concrete cone majorant for the Section 4.7 lower integrand -/

noncomputable section

open MeasureTheory
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding blockRotation_inv_mul_torus determinantNorm_torus determinantNorm_torus_bounds diagonalDensity diagonalDensity_le diagonalDensity_nonneg exists_coefficient_growth exists_coefficient_rootBounded exists_coefficient_torusSize_growth exists_coefficient_torus_growth exists_integrand_torus_majorant exists_rotated_section_growth exists_section_growth exists_standard_functional_growth exists_summable_integrand_majorant instBorelSpaceCarrier instIsNonarchimedeanLocalFieldCarrier instMeasurableSpaceCarrier instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_4 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 integrand_standard_mk isEntryBounded_torus normalizedAbs_uniformizer_zpow torusLevi torusLevi_embedding torusLevi_entryBounded torusLevi_inv_halfModulus_le torusLevi_rotated_twist
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockJacquetConvergenceStatement TwoBlockWhittakerDeformationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantComplexPower_upperUnipotent determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockDeformedBlocks twoBlockDeformedBlocks_zero twoBlockDeformedInduced twoBlockJacquetConvergence twoBlockOppositeTwistBlocks twoBlockOppositeTwistBlocks_apply twoBlockOppositeTwistBlocks_isOfWhittakerType_iff twoBlockOppositeTwistFunctional twoBlockOppositeTwistFunctional_val zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement exists_rowSchwartz_order_lower_bound padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
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
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding blockRotation_inv_mem_integralOpen blockRotation_inv_mul_mem_integralOpen blockRotation_mem_integralOpen canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding blockRotation_inv_mul_diagonal exists_partialSection_diagonal_bounds exists_partialSection_diagonal_compact_bounds exists_partialSection_rotated_diagonal_compact_bounds exists_partialSection_rotated_torus_compact_bounds groupIntegrand groupIntegrand_def groupIntegrand_lowerBlockUnipotent_mul integrand integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_diagonal partialSection_lowerBlockUnipotent_mul partialSection_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_lowerBlockUnipotent_mul sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding

universe uF uV uW

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Moving the inverse block rotation through the canonical torus permutes its
integer exponents. -/
theorem blockRotation_inv_mul_torus (lam : Fin (t + 1) → ℤ) :
    (blockRotation h F)⁻¹ * Iwasawa.torus
        (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam =
      Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
        (rotatedExponents h lam) * (blockRotation h F)⁻¹ :=
  blockRotation_inv_mul_diagonal h _

/-- Section growth in the rotated coordinates, with the exact opposing twist
and all remaining diagonal growth absorbed into a single fixed base. -/
theorem exists_rotated_section_growth (ψ : UnitaryAdditiveCharacter F)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (j : Fin t) (hj : j.val = m 1) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (u : ℝ)
      (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u)),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam : Fin (t + 1) → ℤ)
        (k : GeneralLinear (t + 1) F), k ∈ integralOpen F t →
        ‖scalarSection
          (fun i => (twoBlockOppositeTwistFunctional F m ψ τ u i (ell i)).val) f
          ((blockRotation h F)⁻¹ * Iwasawa.torus
            (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * k) 1‖ ≤
          C * B ^ torusSize lam *
            ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
              (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ)) := by
  obtain ⟨B, hB, hgrowth⟩ := exists_section_growth F h ψ τ hτ ell
  let q : ℝ := (⟨⟩ : LocalFieldData F).residueCardinality
  let D : ℝ := q ^ ((m 0 + 1) * (m 1 + 1))
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  have hD : 1 ≤ D := one_le_pow₀ hq.le
  refine ⟨B * D, one_le_mul_of_one_le_of_one_le hB hD, fun u f => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hgrowth u f
  refine ⟨C, hC0, fun lam k hk => ?_⟩
  have hb := hC ((blockRotation h F)⁻¹ * k)
    (blockRotation_inv_mul_mem_integralOpen F h hk)
    (torusSize (rotatedExponents h lam)) (torusLevi F h (rotatedExponents h lam))
    (torusLevi_entryBounded F h (rotatedExponents h lam))
  rw [torusLevi_embedding, torusSize_rotatedExponents,
    torusLevi_rotated_twist h F lam j hj u] at hb
  have heq : (blockRotation h F)⁻¹ * Iwasawa.torus
      (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F)) lam * k =
      Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit (⟨⟩ : LocalFieldData F))
        (rotatedExponents h lam) * ((blockRotation h F)⁻¹ * k) := by
    rw [blockRotation_inv_mul_torus, mul_assoc]
  rw [heq]
  have hm := torusLevi_inv_halfModulus_le F h (rotatedExponents h lam)
  rw [torusSize_rotatedExponents] at hm
  calc
    _ ≤ C * B ^ torusSize lam *
        ‖(((⟨⟩ : LocalFieldData F).leviHalfModulus (succBlockShape m h)
          (torusLevi F h (rotatedExponents h lam)) : ℂˣ) : ℂ)⁻¹‖ *
        q ^ (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ)) := hb
    _ ≤ C * B ^ torusSize lam * D ^ torusSize lam *
        q ^ (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ)) := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩

/-- Exact representative formula for the integrand transported to the standard
quotient. The test coefficient is evaluated without a left rotation. -/
theorem integrand_standard_mk (ψ : UnitaryAdditiveCharacter F)
    {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i)}
    (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
    (Wtest : WhittakerFunctions ψ t) (Φ : SchwartzBruhat (Fin (t + 1) → F))
    (μ : AdditiveHaarMeasure F) (g : GeneralLinear (t + 1) F) :
    integrand ell f Wtest Φ μ
        ((lowerToStandard h F).symm (Quotient.mk _ g)) =
      Wtest.val g * scalarSection (fun i => (ell i).val) f
        ((blockRotation h F)⁻¹ * g) 1 *
      partialSection h ψ μ Φ ((blockRotation h F)⁻¹ * g) := by
  rw [lowerToStandard_symm_mk, integrand_mk, mul_inv_cancel_left]

/-- One fixed growth base works for every later section, coefficient and row
Schwartz function. Nonzero values are confined to an opposing cone. -/
theorem exists_integrand_torus_majorant (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + 1) F) V)
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (lambda : glFunctionals ψ t π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (j : Fin t) (hj : j.val = m 1) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (u : ℝ)
      (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
      (Wtest : (coefficientModel π lambda).toSubmodule)
      (Φ : SchwartzBruhat (Fin (t + 1) → F)),
      ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧
        ∀ (lam : Fin (t + 1) → ℤ) (k : GeneralLinear (t + 1) F),
          k ∈ integralOpen F t →
          let z := (lowerToStandard h F).symm (Quotient.mk _
            (Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
              (⟨⟩ : LocalFieldData F)) lam * k))
          let E := integrand
            (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i))
            f Wtest.val Φ ν.val
          ‖E z‖ ≤ C * B ^ torusSize lam *
            ((⟨⟩ : LocalFieldData F).residueCardinality : ℝ) ^
              (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ)) ∧
          (E z ≠ 0 → OppositeCone M (Finset.Iic j.castSucc) lam) := by
  obtain ⟨Bs, hBs, hsection⟩ := exists_rotated_section_growth F h ψ τ hτ ell j hj
  obtain ⟨Bw, hBw, hcoeff⟩ := exists_coefficient_torusSize_growth F ψ π hπ lambda
  let q : ℝ := (⟨⟩ : LocalFieldData F).residueCardinality
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  refine ⟨Bw * Bs * q,
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hBw hBs) hq.le,
    fun u f Wtest Φ => ?_⟩
  obtain ⟨Cs, hCs0, hCs⟩ := hsection u f
  obtain ⟨Cw, hCw0, hCw⟩ := hcoeff Wtest 1
  obtain ⟨L, hL⟩ := exists_coefficient_rootBounded F ψ π hπ.1.1 lambda Wtest
  obtain ⟨Cf, M, hCf0, hCf⟩ :=
    exists_partialSection_rotated_torus_compact_bounds h ψ ν.val Φ ν.property
      (integralOpen F t) (isCompact_integralOpen F t) j hj
  refine ⟨Cw * Cs * Cf, M + t * L, by positivity, fun lam k hk => ?_⟩
  dsimp only
  rw [integrand_standard_mk]
  simp only [← mul_assoc]
  have hs := hCs lam k hk
  have hw := hCw lam k hk
  simp only [one_mul] at hw
  have hf := hCf lam k hk
  constructor
  · rw [norm_mul, norm_mul]
    calc
      _ ≤ (Cw * Bw ^ torusSize lam) *
          (Cs * Bs ^ torusSize lam * q ^
            (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ))) *
          (Cf * q ^ torusSize lam) := by
        exact mul_le_mul
          (mul_le_mul hw hs (norm_nonneg _) (by positivity)) hf.1
          (norm_nonneg _) (by positivity)
      _ = _ := by simp only [mul_pow]; ring
  · intro hne
    have hwne := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hne).1).1
    have hfne := (mul_ne_zero_iff.mp hne).2
    obtain ⟨hhi, hlo⟩ := hf.2 hfne
    exact oppositeCone_of_endpoints (hL lam k hk hwne) j hlo hhi

theorem diagonalDensity_nonneg {n : ℕ} (lam : Fin n → ℤ) :
    0 ≤ diagonalDensity F lam :=
  inv_nonneg.mpr (Finset.prod_nonneg (fun _ _ => Finset.prod_nonneg
    (fun _ _ => (⟨⟩ : LocalFieldData F).normalizedAbs_nonneg _)))

/-- A single real threshold, before all later analytic inputs, yields a uniform
compact bound whose product with the exact Iwasawa density is summable. -/
theorem exists_summable_integrand_majorant (ψ : UnitaryAdditiveCharacter F)
    (ν : Langlands.AllField.LocalFactor.PadicAbelian.SelfDualHaar (⟨⟩ : LocalFieldData F) ψ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + 1) F) V)
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (lambda : glFunctionals ψ t π)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (j : Fin t) (hj : j.val = m 1) :
    ∃ C : ℝ, ∀ (u : ℝ), C < u →
      ∀ (f : Sections F h (twoBlockOppositeTwistBlocks F m τ u))
        (Wtest : (coefficientModel π lambda).toSubmodule)
        (Φ : SchwartzBruhat (Fin (t + 1) → F)),
      ∃ A : (Fin (t + 1) → ℤ) → ℝ,
        (∀ lam, 0 ≤ A lam) ∧
        Summable (fun lam => diagonalDensity F lam * A lam) ∧
        ∀ (lam : Fin (t + 1) → ℤ) (k : GeneralLinear (t + 1) F),
          k ∈ integralOpen F t →
          ‖integrand
            (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i))
            f Wtest.val Φ ν.val
            ((lowerToStandard h F).symm (Quotient.mk _
              (Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
                (⟨⟩ : LocalFieldData F)) lam * k)))‖ ≤ A lam := by
  classical
  obtain ⟨B, hB, hbound⟩ := exists_integrand_torus_majorant F h ψ ν π hπ lambda τ hτ ell j hj
  let q : ℝ := (⟨⟩ : LocalFieldData F).residueCardinality
  let D : ℝ := q ^ (2 * (t + 1) * (t + 1))
  have hq : 1 < q := by
    dsimp only [q]
    exact_mod_cast (⟨⟩ : LocalFieldData F).residueCardinality_gt_one
  have hD : 1 ≤ D := one_le_pow₀ hq.le
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨C, _, hC⟩ := exists_geometric_twist_threshold (B := D * B) hq
  refine ⟨C, fun u hu f Wtest Φ => ?_⟩
  obtain ⟨hu0, hr⟩ := hC u hu
  obtain ⟨K, M, hK0, hK⟩ := hbound u f Wtest Φ
  refine ⟨coneMajorant (Finset.Iic j.castSucc) K B q u M,
    coneMajorant_nonneg _ hK0 hB0 (zero_le_one.trans hq.le), ?_, ?_⟩
  · apply Summable.of_nonneg_of_le
      (fun lam => mul_nonneg (diagonalDensity_nonneg F lam)
        (coneMajorant_nonneg _ hK0 hB0 (zero_le_one.trans hq.le) lam)) _
      ((summable_cone_twist (M := M) (Finset.Iic j.castSucc) hq
        (mul_nonneg (zero_le_one.trans hD) hB0) hu0 hr).mul_left K)
    intro lam
    unfold coneMajorant
    split_ifs with hc
    · calc
        _ ≤ D ^ torusSize lam * (K * B ^ torusSize lam *
            q ^ (-u * (twistDegree (Finset.Iic j.castSucc) lam : ℝ))) :=
          mul_le_mul_of_nonneg_right (diagonalDensity_le F lam) (by positivity)
        _ = _ := by rw [mul_pow]; ring
    · simp
  · intro lam k hk
    obtain ⟨hb, hs⟩ := hK lam k hk
    unfold coneMajorant
    split_ifs with hc
    · exact hb
    · have hz : integrand
          (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell i))
          f Wtest.val Φ ν.val
          ((lowerToStandard h F).symm (Quotient.mk _
            (Iwasawa.torus (Langlands.LocalFactor.LocalAbelian.uniformizerUnit
              (⟨⟩ : LocalFieldData F)) lam * k))) = 0 := by
        by_contra he
        exact hc (hs he)
      rw [hz, norm_zero]

end Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
