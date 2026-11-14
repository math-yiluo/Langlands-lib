import Langlands.Representation.RankinSelberg.TwoBlockUnipotentFiberProper
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentFiberKernel
/-!
# Compact finiteness and s-finiteness of the radical fiber kernel
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding FiberKernelSFiniteStatement continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul fiberKernel fiberKernel_compact_ne_top fiberKernel_isSFinite fiberKernel_mk fiberMeasures_upperUnipotent_mul isClopen_determinantSlice map_unipotentShift measurableSet_determinantSlice measurable_fiberMeasures mk_mem_determinantSlice radicalAverage radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice

open _root_.MeasureTheory ProbabilityTheory Set
open Langlands.GeneralLinear hiding blockUnipotent
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockJacquet hiding IsAbsIntegrable IsAbsIntegrableAt Sections inducedRep integrand integrand_add integrand_apply integrand_def integrand_inducedRep integrand_smul jacquetFunction jacquetFunction_add jacquetFunction_apply jacquetFunction_def jacquetFunction_inducedRep jacquetFunction_smul scalarSection scalarSection_add scalarSection_covariant scalarSection_def scalarSection_inducedRep scalarSection_one scalarSection_smul sectionEval sectionEval_add sectionEval_smul sectionEval_zero
open Langlands.AllField.RankinSelberg.TwoBlockJacquet
open Langlands.RankinSelberg.TwoBlockDeformation hiding compactRadicalJacquet compactRadicalJacquet_inducedRep compactRadicalSubmodule determinantNorm_eq_one_of_mem_upperUnipotent inducedRep_mem_compactRadicalSubmodule integral_comp_unipotentShift inverseStandardCharacter_eq_prod isAbsIntegrableAt_one_of_mem_compactRadicalSubmodule jacquetFunction_inducedRep_upperUnipotent leviModulus_eq_one mem_compactRadicalSubmodule radicalRestriction radicalRestriction_inducedRep sectionEval_leviEmbedding_mul tensorContraction_blockTensor
open Langlands.AllField.RankinSelberg.TwoBlockDeformation
open Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegration

universe uK uF

section Topology


end Topology

section Canonical

variable (F : Type uF) [Field F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- Every fiber of the actual radical kernel is finite on compact sets. -/
theorem fiberKernel_compact_ne_top [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] :
    ∀ [MeasurableSpace F] [BorelSpace F]
      [MeasurableSpace (GeneralLinear (t + 1) F)]
      [BorelSpace (GeneralLinear (t + 1) F)]
      [MeasurableSpace (LeftUnipotentQuotient t F)]
      [BorelSpace (LeftUnipotentQuotient t F)]
      [MeasurableSpace (BlockQuotient h F)] [BorelSpace (BlockQuotient h F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
      [μ.IsAddHaarMeasure] (q : LeftUnipotentQuotient t F)
      (S : Set (BlockQuotient h F)), IsCompact S →
      fiberKernel F h μ q S ≠ ⊤ := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1)
  intro _ _ _ _ _ _ _ _ μ _ q S hS
  let : LocallyCompactSpace (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F) :=
    inferInstanceAs (LocallyCompactSpace (Fin (m 0 + 1) → Fin (m 1 + 1) → F))
  let := leftQuotient_t2Space (blockUnipotent h F) (isClosed_blockUnipotent h F)
  refine Quotient.inductionOn q fun g => ?_
  have hf : Measurable (fun x => fiberPoint h F x g) :=
    ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  rw [fiberKernel_mk F h μ g, Measure.map_apply hf hS.measurableSet]
  exact (fiberPoint_isCompact_preimage h g hS).measure_ne_top

/-- S-finiteness of the actual radical kernel for every supplied rectangular Haar. -/
def FiberKernelSFiniteStatement [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : Prop :=
    ∀ [MeasurableSpace F] [BorelSpace F]
      [MeasurableSpace (GeneralLinear (t + 1) F)]
      [BorelSpace (GeneralLinear (t + 1) F)]
      [MeasurableSpace (LeftUnipotentQuotient t F)]
      [BorelSpace (LeftUnipotentQuotient t F)]
      [MeasurableSpace (BlockQuotient h F)] [BorelSpace (BlockQuotient h F)]
      (μ : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F))
      [μ.IsAddHaarMeasure],
      IsSFiniteKernel (fiberKernel F h μ)

/-- Compact finiteness and a common countable compact cover of the block quotient
prove s-finiteness of the measurable radical kernel. -/
theorem fiberKernel_isSFinite [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] : FiberKernelSFiniteStatement F h := by
  unfold FiberKernelSFiniteStatement
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
  let H := blockUnipotent h F
  let := leftQuotient_t2Space H (isClosed_blockUnipotent h F)
  let := leftQuotient_locallyCompactSpace H
  let := _root_.Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  exact kernel_isSFinite_of_compact_finite (fiberKernel F h μ)
    (fiberKernel_compact_ne_top F h μ)

end Canonical

end Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
