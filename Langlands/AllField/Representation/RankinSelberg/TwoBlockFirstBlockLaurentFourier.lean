import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentFourier
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnfoldingIntegrandData
/-!
# The partial Fourier value on the first-block fiber

At `diag(v, 1) g` the plus-sign first-block partial Fourier value of `gΦ` is
`|det v|⁻¹ ∫ ψ((x v⁻¹)_0) Φ((x, η) g) dx`, for the supplied self-dual product measure.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg.TwoBlockFirstBlockLaurent hiding partialSection_firstBlockEmbedding_mul
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.RankinSelberg.TwoBlockFirstBlockQuotient hiding MixedQuotient NormOneRightInvariant blockUnipotent_le_mixedSubgroup continuous_determinantOrder continuous_fiberPoint determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice determinant_mixedEmbedding fiberIntegral fiberIntegral_def fiberIntegral_mixedEmbedding_mul fiberIntegral_mixedSubgroup_mul fiberPoint_mem_determinantSlice_iff fiberPoint_mixedEmbedding_mul firstBlockAverage firstBlockAverage_mk isClopen_determinantSlice isClosed_mixedSubgroup measurableSet_determinantSlice mem_determinantSlice mem_mixedSubgroup_iff mem_mixedSubgroup_iff_determinantNorm mem_normOneSubgroup_iff mem_normOneSubgroup_iff_normalizedAbs mixedCoordinates mixedCoordinates_mixedEmbedding mixedEmbedding mixedEmbedding_apply mixedEmbedding_index_one_one mixedEmbedding_index_one_zero mixedEmbedding_index_zero_one mixedEmbedding_index_zero_zero mixedEmbedding_mem mixedEmbedding_mixedCoordinates mixedSubgroup mixedSubgroupEquiv mixedSubgroupEquiv_apply_val mixedSubgroupHomeomorph mixedSubgroup_le_normOneSubgroup mixedSubgroup_le_parabolic mk_mem_determinantSlice normOneRightInvariant_of_isCompatible normOneSubgroup ord_determinant_eq_zero rightTranslate_mem_determinantSlice
open Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice
open Langlands.HarmonicAnalysis hiding PadicRowFourierEquivarianceStatement padicRectangularHaarScaling padicRowFourierEquivariance padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis.TwoBlockRowPartialFourier
open Langlands.RankinSelberg.TwoBlockLowerUnfolding hiding groupIntegrand groupIntegrand_def groupIntegrand_lowerBlockUnipotent_mul integrand integrand_mk integrand_mk_eq_groupIntegrand isTopologicalRing_carrier partialSection partialSection_apply partialSection_lowerBlockUnipotent_mul rowMeasure_map_vecMul_upperUnipotent scalarSection_lowerBlockUnipotent_mul sigmaFinite_additiveHaarMeasure whittaker_blockRotation_lowerBlockUnipotent_mul
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnfolding

universe uF

variable {F : Type uF} [Field F]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- `(diag(v, 1) g Φ)~[ζ, η] = |det v|⁻¹ ∫ ψ((x v⁻¹)_0) Φ((x, η) g) dx`. -/
theorem partialSection_firstBlockEmbedding_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
      (Φ : SchwartzBruhat (Fin (t + 1) → F))
      (v : GeneralLinear (m 0 + 1) F) (g : GeneralLinear (t + 1) F),
      partialSection h ψ μ Φ (firstBlockEmbedding h F v * g) =
        (((⟨⟩ : LocalFieldData F).normalizedAbs (Matrix.det v.val))⁻¹ : ℂ) *
          ∫ x, ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
            Φ (Matrix.vecMul (join (succBlockEquiv h) x (eta (m 1))) g.val)
            ∂rowMeasure μ (m 0 + 1) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  intro ψ μ Φ v g
  have := sigmaFinite_additiveHaarMeasure μ
  have hχ (a : F) (ha : a ≠ 0) :
      μ.measure.map (fun x => a * x) = (T.normalizedAbsHom a)⁻¹ • μ.measure :=
    padicScalarHaarScaling F T μ.measure (Units.mk0 a ha)
  let H : (Fin (m 0 + 1) → F) → ℂ := fun x =>
    ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
      Φ (Matrix.vecMul (join (succBlockEquiv h) x (eta (m 1))) g.val)
  have hL : MeasurableEmbedding (fun x : Fin (m 0 + 1) → F => Matrix.vecMul x v.val) :=
    (rowHomeomorph v).measurableEmbedding
  rw [partialSection_apply]
  calc (∫ w, ψ.complex (w 0) *
        Φ (Matrix.vecMul (join (succBlockEquiv h) w (eta (m 1)))
          (firstBlockEmbedding h F v * g).val) ∂rowMeasure μ (m 0 + 1))
      = ∫ w, H (Matrix.vecMul w v.val) ∂rowMeasure μ (m 0 + 1) := by
        congr 1
        funext w
        simp only [H]
        rw [Units.val_mul, ← Matrix.vecMul_vecMul, vecMul_join_eta_firstBlockEmbedding,
          Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
          Matrix.vecMul_one]
    _ = ∫ z, H z ∂((rowMeasure μ (m 0 + 1)).map fun x => Matrix.vecMul x v.val) :=
        (hL.integral_map H).symm
    _ = ∫ z, H z ∂((T.normalizedAbsHom (Matrix.det v.val))⁻¹ • rowMeasure μ (m 0 + 1)) := by
        rw [rowMeasure_map_vecMul T.normalizedAbsHom μ hχ v]
    _ = _ := by
        rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul, NNReal.coe_inv,
          Complex.ofReal_inv]
        rfl

end Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent
