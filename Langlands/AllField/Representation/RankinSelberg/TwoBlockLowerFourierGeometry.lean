import Langlands.Representation.RankinSelberg.TwoBlockLowerFourierGeometry
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
/-! # Actual quotient geometry for lower Fourier transport -/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFourier
open Langlands.RankinSelberg.TwoBlockLowerFourier hiding lowerDuality_order lowerDuality_slices lowerDuality_symm_order ord_determinant_dual ord_determinant_weylLong
open Langlands.AllField.RankinSelberg.TwoBlockLowerFourier
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.QuotientIntegration
open Langlands.Whittaker hiding TwoBlockCellUnipotentStabilityStatement TwoBlockInducedCarrier exchangedParabolic hasCompactSupport_twoBlockCellRestriction mul_upperUnipotent_mem_twoBlockCell swapRank_exchangedParabolic twoBlockCell twoBlockCellInclusion twoBlockCellInclusion_apply twoBlockCellPoint twoBlockCellPoint_mul_upperUnipotent twoBlockCellRestriction twoBlockCellSubmodule twoBlockCellUnipotentStability twoBlockEval twoBlockInduced twoBlockInducingRepresentation twoBlockParabolic twoBlockRestriction unipotentLeviFactor unipotentShift
open Langlands.AllField.Whittaker

universe uR uF

section Algebra


end Algebra

section Topology



end Topology

section Orders

variable (F : Type uF) [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

theorem ord_determinant_weylLong [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    (⟨⟩ : LocalFieldData F).ord
      (determinant (weylLong (t + 1) F) : F) = 0 := by
  have hd : (determinant (weylLong (t + 1) F) : F) *
      (determinant (weylLong (t + 1) F) : F) = 1 := by
    rw [← Units.val_mul, ← map_mul, weylLong_mul_self, map_one, Units.val_one]
  have hm := (⟨⟩ : LocalFieldData F).ord_mul
    (determinant (weylLong (t + 1) F)).ne_zero
    (determinant (weylLong (t + 1) F)).ne_zero
  rw [hd, (⟨⟩ : LocalFieldData F).ord_one] at hm
  omega

theorem ord_determinant_dual [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (g : GeneralLinear (t + 1) F) :
    (⟨⟩ : LocalFieldData F).ord
      (determinant (weylLong (t + 1) F *
        inverseTranspose (t + 1) F g) : F) =
      -(⟨⟩ : LocalFieldData F).ord (determinant g : F) := by
  have hi : (determinant (inverseTranspose (t + 1) F g) : F) =
      (determinant g : F)⁻¹ := by
    change Matrix.det (g⁻¹).val.transpose = _
    rw [Matrix.det_transpose]
    simpa only [Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply] using
      congrArg Units.val (map_inv determinant g)
  rw [map_mul, Units.val_mul, (⟨⟩ : LocalFieldData F).ord_mul
    (determinant _).ne_zero (determinant _).ne_zero,
    ord_determinant_weylLong, zero_add, hi, (⟨⟩ : LocalFieldData F).ord_inv]

theorem lowerDuality_order [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ z : LowerQuotient h F,
      Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder F (reverse_sum h) (lowerDuality F h z) =
        -Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder F h z := by
  intro z
  induction z using Quotient.inductionOn with
  | h g =>
    rw [lowerDuality_mk, Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder_mk, Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder_mk]
    exact ord_determinant_dual F g

theorem lowerDuality_symm_order [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ z : LowerQuotient (reverse_sum h) F,
      Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder F h ((lowerDuality F h).symm z) =
        -Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder F (reverse_sum h) z := by
  intro z
  induction z using Quotient.inductionOn with
  | h g =>
    rw [lowerDuality_symm_mk, Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder_mk, Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantOrder_mk]
    exact ord_determinant_dual F g

theorem lowerDuality_slices [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ k : ℤ,
      lowerDuality F h '' Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k =
          Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) ∧
      lowerDuality F h ⁻¹' Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) =
          Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k ∧
      (lowerDuality F h).symm '' Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) =
          Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k ∧
      (lowerDuality F h).symm ⁻¹' Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k =
          Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) := by
  intro k
  have hp : lowerDuality F h ⁻¹' Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) =
      Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k := by
    ext z
    simp only [Set.mem_preimage, Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder,
      lowerDuality_order, neg_inj]
  have hps : (lowerDuality F h).symm ⁻¹' Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k =
      Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F (reverse_sum h) (-k) := by
    ext z
    simp only [Set.mem_preimage, Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.mem_determinantSlice_iff_determinantOrder,
      lowerDuality_symm_order]
    omega
  refine ⟨?_, hp, ?_, hps⟩
  · rw [← hp]
    exact (lowerDuality F h).image_preimage _
  · rw [← hps]
    exact (lowerDuality F h).symm.image_preimage _

end Orders

end Langlands.AllField.RankinSelberg.TwoBlockLowerFourier
