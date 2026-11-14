import Langlands.Representation.RankinSelberg.TwoBlockUnipotentFiberKernel
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
/-!
# The actual two-block radical fiber kernel
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul fiberKernel fiberKernel_mk fiberMeasures_upperUnipotent_mul isClopen_determinantSlice map_unipotentShift measurableSet_determinantSlice measurable_fiberMeasures mk_mem_determinantSlice radicalAverage radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear hiding blockUnipotent
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open scoped ENNReal

universe uF

variable (F : Type uF) [Field F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- The affine radical coordinate change induced by an upper unipotent
matrix preserves the supplied additive Haar measure. -/
theorem map_unipotentShift [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [MeasurableSpace F] [BorelSpace F]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
      [μ.IsAddHaarMeasure] (n : upperUnipotent (t + 1) F),
      Measure.map (unipotentShift h n) μ = μ := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  intro _ _ μ _ n
  let e := Shahidi.rectangularConj (unipotentLevi h n 0) (unipotentLevi h n 1)
  let a : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F :=
    ((unipotentLevi h n 0)⁻¹ : GeneralLinear (m 0 + 1) F).val * unipotentCorner h n
  have hμ : μ.map e = μ := by
    simpa only [determinantNorm_eq_one_of_mem_upperUnipotent F _ (unipotentLevi_mem h n 0),
      determinantNorm_eq_one_of_mem_upperUnipotent F _ (unipotentLevi_mem h n 1),
      Units.val_one, one_pow, div_one, one_smul] using
      Langlands.AllField.Shahidi.map_rectangularConj_padic F T μ (unipotentLevi h n 0) (unipotentLevi h n 1)
  have hshift : unipotentShift h n = (fun x => a + x) ∘ e := by
    funext x
    simp only [Function.comp_apply, unipotentShift, e, Shahidi.rectangularConj_apply, a]
    rw [Matrix.mul_add, Matrix.mul_assoc]
  rw [hshift, ← Measure.map_map (measurable_const_add a) e.measurable, hμ,
    map_add_left_eq_self]

/-- Joint measurability makes the representative fiber measures measurable
as a map from the ambient group to the space of measures. -/
theorem measurable_fiberMeasures [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [MeasurableSpace F] [BorelSpace F]
      [MeasurableSpace (GeneralLinear (t + 1) F)]
      [BorelSpace (GeneralLinear (t + 1) F)]
      [MeasurableSpace (BlockQuotient h F)] [BorelSpace (BlockQuotient h F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F)) [SFinite μ],
      Measurable (fun g => Measure.map (fun x => fiberPoint h F x g) μ) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.secondCountableTopology
  let := T.generalLinearSecondCountableTopology (t + 1)
  intro _ _ _ _ _ _ μ _
  have hf := (continuous_fiberPoint F h).measurable
  have hm := (Measure.measurable_map _ hf).comp (Measurable.map_prodMk_right (μ := μ))
  simpa only [Measure.map_map hf measurable_prodMk_right, Function.comp_def,
    Function.uncurry_apply_pair] using hm

/-- The representative fiber measures are invariant under changing the
representative by left multiplication from the full unipotent subgroup. -/
theorem fiberMeasures_upperUnipotent_mul [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [MeasurableSpace F] [BorelSpace F]
      [MeasurableSpace (BlockQuotient h F)] [BorelSpace (BlockQuotient h F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
      [μ.IsAddHaarMeasure] (n : upperUnipotent (t + 1) F)
      (g : GeneralLinear (t + 1) F),
      Measure.map (fun x => fiberPoint h F x (n.val * g)) μ =
        Measure.map (fun x => fiberPoint h F x g) μ := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.secondCountableTopology
  intro _ _ _ _ μ _ n g
  have hshift : Measurable (unipotentShift h n) := by
    let := T.valuativeRel
    let := T.localField
    have hs : Continuous (unipotentShift h n) := continuous_const.matrix_mul
      (continuous_const.add (continuous_id.matrix_mul continuous_const))
    exact hs.measurable
  have hf : Measurable (fun x => fiberPoint h F x g) :=
    ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  simp only [fiberPoint_upperUnipotent_mul]
  change Measure.map ((fun x => fiberPoint h F x g) ∘ unipotentShift h n) μ = _
  rw [← Measure.map_map hf hshift, map_unipotentShift F h μ n]

/-- The actual descended measure kernel. Its value is the prescribed
pushforward of the supplied radical measure, without normalization. -/
def fiberKernel [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [MeasurableSpace F] [BorelSpace F]
      [MeasurableSpace (GeneralLinear (t + 1) F)]
      [BorelSpace (GeneralLinear (t + 1) F)]
      [MeasurableSpace (LeftUnipotentQuotient t F)]
      [BorelSpace (LeftUnipotentQuotient t F)]
      [MeasurableSpace (BlockQuotient h F)] [BorelSpace (BlockQuotient h F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
      [μ.IsAddHaarMeasure],
      Kernel (LeftUnipotentQuotient t F) (BlockQuotient h F) := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1)
  let := T.generalLinearSecondCountableTopology (t + 1)
  intro _ _ _ _ _ _ _ _ μ _
  let : LocallyCompactSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (m 0 + 1) → Fin (m 1 + 1) → F))
  let : SecondCountableTopology (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    inferInstanceAs (SecondCountableTopology (Fin (m 0 + 1) → Fin (m 1 + 1) → F))
  let k := descend (upperUnipotent (t + 1) F)
    (fun g => Measure.map (fun x => fiberPoint h F x g) μ)
    (fiberMeasures_upperUnipotent_mul F h μ)
  refine ⟨k, (measurable_quotient_iff _ (UpperUnipotent.isClosed (R := F)) k).2 ?_⟩
  exact measurable_fiberMeasures F h μ

/-- Representative evaluation of the descended kernel is exact. -/
theorem fiberKernel_mk [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [MeasurableSpace F] [BorelSpace F]
      [MeasurableSpace (GeneralLinear (t + 1) F)]
      [BorelSpace (GeneralLinear (t + 1) F)]
      [MeasurableSpace (LeftUnipotentQuotient t F)]
      [BorelSpace (LeftUnipotentQuotient t F)]
      [MeasurableSpace (BlockQuotient h F)] [BorelSpace (BlockQuotient h F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
      [μ.IsAddHaarMeasure] (g : GeneralLinear (t + 1) F),
      fiberKernel F h μ (Quotient.mk _ g) =
        Measure.map (fun x => fiberPoint h F x g) μ := by
  intro _ _ _ _ _ _ _ _ μ _ g
  rfl

end Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
