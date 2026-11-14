import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankLastRowReductionProof
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentFiberProper
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentMeasures
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientAnalysis
/-!
# Normalized integration for the two-block unipotent quotient
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement EqualRankLastRowReductionStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockUnipotentQuotientIntegrationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankLastRowReduction equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable twoBlockUnipotentQuotientIntegration zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory ProbabilityTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding FiberKernelSFiniteStatement analytic_of_comp_eq_smul continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul fiberKernel fiberKernel_compact_ne_top fiberKernel_isSFinite fiberKernel_mk fiberMeasures_upperUnipotent_mul iUnion_determinantSlice integerCube_mass_pos_lt_top isClopen_determinantSlice map_unipotentShift measurableSet_determinantSlice measurable_fiberMeasures mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice radicalAverage radicalAverage_eq_integral_kernel radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient hiding determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open Langlands.RankinSelberg.TwoBlockUnipotentQuotientIntegration
open scoped ENNReal

universe uF

/-- The normalized quotient tower and its Tonelli and Bochner consequences,
for the actual two-block radical kernel and every supplied rectangular Haar. -/
theorem twoBlockUnipotentQuotientIntegration :
    TwoBlockUnipotentQuotientIntegrationStatement.{uF} := by
  intro F _ _ _ _ t m h
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.generalLinearTopologicalGroup (t + 1)
  let := T.generalLinearLocallyCompactSpace (t + 1)
  let := T.generalLinearSecondCountableTopology (t + 1)
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let G := GeneralLinear (t + 1) F
  let N := upperUnipotent (t + 1) F
  let H := blockUnipotent h F
  let NQ := LeftUnipotentQuotient t F
  let HQ := BlockQuotient h F
  let R := Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : MeasurableSpace N := borel N
  let : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F) :=
    fun i => borel (upperUnipotent (m i + 1) F)
  let : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F) :=
    fun _ => ⟨rfl⟩
  let : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F) :=
    fun i => by
      let := T.generalLinearSecondCountableTopology (m i + 1)
      exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
  let : BorelSpace (BlockUnipotents m F) := inferInstance
  let : BorelSpace R := inferInstance
  let : MeasurableSpace NQ := borel NQ
  let : BorelSpace NQ := ⟨rfl⟩
  let : MeasurableSpace HQ := borel HQ
  let : BorelSpace HQ := ⟨rfl⟩
  let μG : Measure G := generalLinearHaar F t
  let μN : Measure N := unipotentHaar F t
  let μH : Measure H := blockHaar F h
  change μH.IsHaarMeasure ∧ μH.Regular ∧ _
  have hN : Measure.IsMulRightInvariant μN := inferInstance
  have hH : Measure.IsMulRightInvariant μH := inferInstance
  refine ⟨inferInstance, inferInstance, hN, hH, ?_⟩
  let := hN
  let := hH
  refine ⟨fullUnipotent_compatibleMeasureExists F t,
    block_compatibleMeasureExists F h, ?_⟩
  intro μR _
  obtain ⟨hc0, hc⟩ := integerCube_mass_pos_lt_top F (m 0 + 1) (m 1 + 1) μR
  let c : ℝ≥0∞ := μR {x | ∀ a b, x a b ∈ (ValuativeRel.valuation F).integer}
  let κ := fiberKernel F h μR
  have : IsSFiniteKernel κ := fiberKernel_isSFinite F h μR
  have hκ : ∀ g : G, κ (Quotient.mk _ g) =
      Measure.map (fun x => fiberPoint h F x g) μR :=
    fiberKernel_mk F h μR
  refine ⟨hc0, hc, κ, inferInstance, hκ, ?_⟩
  intro νN νH hνN hνH
  have hνN' : IsCompatible N μG μN νN := hνN
  have hνH' : IsCompatible H μG μH νH := hνH
  let := leftQuotient_locallyCompactSpace N
  let := leftQuotient_locallyCompactSpace H
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap N)
  let := Topology.IsOpenQuotientMap.secondCountableTopology
    (leftQuotient_isOpenQuotientMap H)
  let := hνN'.regular
  let := hνH'.regular
  have : SigmaFinite νN := inferInstance
  have : SigmaFinite νH := inferInstance
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hwhole : κ ∘ₘ νN = c • νH :=
    comp_eq_smul h μG μH (blockMeasure_integral F h) μR hc.ne κ hκ
      νN hνN' νH hνH'
  intro s hs
  have hrestricted := comp_restrict_eq_smul h μR κ hκ νN νH c hwhole s hs
  exact ⟨hrestricted,
    analytic_of_comp_eq_smul F h μR c hc0.ne' hc.ne κ hκ
      (νN.restrict s) (νH.restrict (projection h F ⁻¹' s)) hrestricted⟩

end Langlands.AllField.RankinSelberg
