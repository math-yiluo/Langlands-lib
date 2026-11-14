import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerUnipotentQuotientData
/-!
# Measures and slice transport for the Section 4.7 lower quotient

The lower measure is exactly the pushforward by the inverse block-rotation
homeomorphism. Compatibility and sigma-finiteness follow from the published
normalized standard quotient construction. Restriction commutes with this
pushforward, which transfers absolute integrability and both integrals.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg.TwoBlockLowerFixedSlice hiding compatible_measure_data integrable_lowerMeasure_iff integral_lowerMeasure lowerMeasure lowerMeasure_restrict measureTransportFieldT2 measureTransportFieldTopology measureTransportFieldValuation measureTransportGeneralLinearGroup measureTransportGeneralLinearLocallyCompact measureTransportGeneralLinearSecondCountable measureTransportLocalField sigmaFinite_lowerMeasure
open Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF uE

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance measureTransportFieldT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance measureTransportGeneralLinearGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
local instance measureTransportGeneralLinearLocallyCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance measureTransportGeneralLinearSecondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace (LeftUnipotentQuotient t F)]
  [BorelSpace (LeftUnipotentQuotient t F)]
variable [MeasurableSpace (LowerQuotient h F)]
  [BorelSpace (LowerQuotient h F)]

/-- The measure used on the lower quotient, with exactly the prescribed scale. -/
def lowerMeasure (νN : Measure (LeftUnipotentQuotient t F)) :
    Measure (LowerQuotient h F) :=
  Measure.map (lowerToStandard h F).symm νN

/-- Restricting the transported measure to a determinant slice is the transport
of the standard measure restricted to the corresponding standard slice. -/
theorem lowerMeasure_restrict (νN : Measure (LeftUnipotentQuotient t F)) (k : ℤ) :
    (lowerMeasure F h νN).restrict (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k) =
      Measure.map (lowerToStandard h F).symm
        (νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t k)) := by
  let e := (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv
  have he := e.restrict_map νN (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)
  change (lowerMeasure F h νN).restrict _ =
    Measure.map (lowerToStandard h F).symm
      (νN.restrict ((lowerToStandard h F).symm ⁻¹'
        Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) at he
  rw [preimage_lowerToStandard_symm_determinantSlice] at he
  exact he

/-- Absolute integrability is preserved in both directions by the prescribed
restricted transport; no convergence assumption is hidden in an integral identity. -/
theorem integrable_lowerMeasure_iff
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (νN : Measure (LeftUnipotentQuotient t F))
    (f : LowerQuotient h F → E) (k : ℤ) :
    Integrable f ((lowerMeasure F h νN).restrict
        (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) ↔
      Integrable (fun q => f ((lowerToStandard h F).symm q))
        (νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t k)) := by
  rw [lowerMeasure_restrict]
  exact integrable_map_equiv
    (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv f

/-- Restricted complex and real integral transport, valid for every Banach-valued
function, including the actual integrand and its norm. -/
theorem integral_lowerMeasure
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (νN : Measure (LeftUnipotentQuotient t F))
    (f : LowerQuotient h F → E) (k : ℤ) :
    (∫ z, f z ∂(lowerMeasure F h νN).restrict
        (Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient.determinantSlice F h k)) =
      ∫ q, f ((lowerToStandard h F).symm q)
        ∂νN.restrict (Langlands.AllField.RankinSelberg.determinantSlice (⟨⟩ : LocalFieldData F) t k) := by
  rw [lowerMeasure_restrict]
  exact integral_map_equiv
    (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv f

/-- Sigma-finiteness of a standard quotient measure passes to its lower transport. -/
theorem sigmaFinite_lowerMeasure
    (νN : Measure (LeftUnipotentQuotient t F)) [SigmaFinite νN] :
    SigmaFinite (lowerMeasure F h νN) :=
  (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv.sigmaFinite_map

variable [MeasurableSpace (GeneralLinear (t + 1) F)]
  [BorelSpace (GeneralLinear (t + 1) F)]
variable [MeasurableSpace (upperUnipotent (t + 1) F)]
  [BorelSpace (upperUnipotent (t + 1) F)]

/-- The exact normalized standard quotient measure exists, and every compatible
measure and its prescribed lower transport are sigma-finite. -/
theorem compatible_measure_data :
    ∃ hN : Measure.IsMulRightInvariant (unipotentHaar F t),
      letI := hN
      (∃ νN : Measure (LeftUnipotentQuotient t F),
        IsCompatible (upperUnipotent (t + 1) F)
          (generalLinearHaar F t) (unipotentHaar F t) νN) ∧
      (∀ νN : Measure (LeftUnipotentQuotient t F),
        IsCompatible (upperUnipotent (t + 1) F)
          (generalLinearHaar F t) (unipotentHaar F t) νN →
        SigmaFinite νN ∧ SigmaFinite (lowerMeasure F h νN)) := by
  refine ⟨unipotentHaar_isMulRightInvariant F t, ?_⟩
  refine ⟨unipotent_compatibleMeasureExists F t, ?_⟩
  intro νN hνN
  let := hνN.regular
  let : T2Space (LeftUnipotentQuotient t F) :=
    leftQuotient_t2Space _ (UpperUnipotent.isClosed (R := F))
  let : LocallyCompactSpace (LeftUnipotentQuotient t F) :=
    leftQuotient_locallyCompactSpace _
  let : SecondCountableTopology (LeftUnipotentQuotient t F) :=
    ContinuousConstSMul.secondCountableTopology
  have hσ : SigmaFinite νN := inferInstance
  exact ⟨hσ, sigmaFinite_lowerMeasure F h νN⟩

end Langlands.AllField.RankinSelberg.TwoBlockLowerFixedSlice
