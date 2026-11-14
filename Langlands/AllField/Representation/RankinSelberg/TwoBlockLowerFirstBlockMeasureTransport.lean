import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockMeasureTransport
import Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport
/-!
# The prescribed lower-unipotent Haar and compatible quotient transport

Subgroup elements are transported by inverse conjugation. Quotient classes are
transported by inverse left multiplication by the block rotation.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding lowerHaar lowerHaar_isHaar lowerHaar_isMulRightInvariant lowerHaar_regular lowerMeasureTransportInstance01 lowerMeasureTransportInstance02 lowerMeasureTransportInstance03 lowerMeasureTransportInstance04 lowerMeasureTransportInstance08 lowerMeasureTransportInstance09 lowerMeasureTransportInstance10 lowerMeasureTransportInstance11 lowerMeasureTransportInstance12 lowerMeasureTransportInstance13 lowerMeasureTransportInstance14 lowerMeasureTransportInstance17 lowerMeasureTransportInstance18 lowerMeasureTransportInstance21 lowerMeasureTransportInstance22 lowerMeasureTransportInstance23 lowerMeasureTransportInstance24 lowerMeasure_isCompatible lowerMeasure_sigmaFinite quotientAverage_lower_transport
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding canonicalConjugationHomeomorph canonicalConjugationHomeomorph_toMulEquiv canonicalLowerToStandardHomeomorph continuous_conjugationEquiv_symm_canonical continuous_determinantOrder determinantOrder determinantOrder_apply determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isClosed_lowerBlockUnipotent_canonical isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mem_determinantSlice_iff_determinantOrder mk_mem_determinantSlice ord_determinant_blockRotation pairwise_disjoint_determinantSlice preimage_lowerToStandard_symm_determinantSlice rightTranslate_mem_determinantSlice t2Space_lowerQuotient_canonical
open Langlands.AllField.RankinSelberg.TwoBlockLowerUnipotentQuotient hiding continuous_determinantOrder determinantOrder determinantOrder_mk determinantSlice isClopen_determinantSlice isOpen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice

universe uF

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerMeasureTransportInstance04 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance lowerMeasureTransportInstance08 (n : ℕ) : IsTopologicalGroup (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup n
local instance lowerMeasureTransportInstance09 (n : ℕ) : MeasurableSpace (GeneralLinear n F) := borel _
local instance lowerMeasureTransportInstance10 (n : ℕ) : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
local instance lowerMeasureTransportInstance11 (n : ℕ) : SecondCountableTopology (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSecondCountableTopology n
local instance lowerMeasureTransportInstance12 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F) :=
  (⟨⟩ : LocalFieldData F).generalLinearLocallyCompactSpace n
local instance lowerMeasureTransportInstance13 (n : ℕ) : MeasurableSpace (upperUnipotent n F) := borel _
local instance lowerMeasureTransportInstance14 (n : ℕ) : BorelSpace (upperUnipotent n F) := ⟨rfl⟩
local instance lowerMeasureTransportInstance17 : MeasurableSpace (lowerBlockUnipotent h F) := borel _
local instance lowerMeasureTransportInstance18 : BorelSpace (lowerBlockUnipotent h F) := ⟨rfl⟩

/-- Exactly the prescribed inverse-conjugation transport of the standard Haar. -/
def lowerHaar : Measure (lowerBlockUnipotent h F) :=
  Measure.map (conjugationEquiv h F).symm (unipotentHaar F t)

instance lowerHaar_isHaar : (lowerHaar F h).IsHaarMeasure :=
  (canonicalConjugationHomeomorph F h).symm.isHaarMeasure_map _

instance lowerHaar_regular : (lowerHaar F h).Regular :=
  Measure.Regular.map (canonicalConjugationHomeomorph F h).symm.toHomeomorph

instance lowerHaar_isMulRightInvariant : (lowerHaar F h).IsMulRightInvariant := by
  let e := (canonicalConjugationHomeomorph F h).symm
  let μ := unipotentHaar F t
  have he : Measurable e := e.continuous.measurable
  change (Measure.map e μ).IsMulRightInvariant
  refine ⟨fun g => ?_⟩
  rw [Measure.map_map (measurable_mul_const g) he]
  change Measure.map (fun x => e x * g) μ = Measure.map e μ
  have hcomp : (fun x => e x * g) = e ∘ (fun x => x * e.symm g) := by
    funext x
    simp
  rw [show (fun x => (e x) * g) = _ from hcomp,
    ← Measure.map_map he (measurable_mul_const _), map_mul_right_eq_self]

local instance lowerMeasureTransportInstance21 : MeasurableSpace (LeftUnipotentQuotient t F) := borel _
local instance lowerMeasureTransportInstance22 : BorelSpace (LeftUnipotentQuotient t F) := ⟨rfl⟩
local instance lowerMeasureTransportInstance23 : MeasurableSpace (LowerQuotient h F) := borel _
local instance lowerMeasureTransportInstance24 : BorelSpace (LowerQuotient h F) := ⟨rfl⟩

/-- Exact orbital-average transport through the two different prescribed maps. -/
theorem quotientAverage_lower_transport (f : GeneralLinear (t + 1) F → ℂ)
    (q : LeftUnipotentQuotient t F) :
    quotientAverage (lowerBlockUnipotent h F) (lowerHaar F h) f
        ((lowerToStandard h F).symm q) =
      quotientAverage (upperUnipotent (t + 1) F) (unipotentHaar F t)
        (fun x => f ((blockRotation h F)⁻¹ * x)) q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [lowerToStandard_symm_mk, quotientAverage_mk, quotientAverage_mk, lowerHaar]
    erw [integral_map_equiv (μ := unipotentHaar F t)
      (canonicalConjugationHomeomorph F h).symm.toHomeomorph.toMeasurableEquiv
      (fun a => f (a.val * ((blockRotation h F)⁻¹ * g)))]
    apply integral_congr_ae
    filter_upwards [] with n
    congr 1
    change ((blockRotation h F)⁻¹ * n.val * blockRotation h F) *
      ((blockRotation h F)⁻¹ * g) = (blockRotation h F)⁻¹ * (n.val * g)
    group

/-- Every compatible standard quotient measure has the required compatible
inverse-left-translation transport, with exactly the inverse-conjugation Haar. -/
theorem lowerMeasure_isCompatible
    (νN : Measure (LeftUnipotentQuotient t F))
    (hνN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) νN) :
    IsCompatible (lowerBlockUnipotent h F)
      (generalLinearHaar F t) (lowerHaar F h)
      (Measure.map (lowerToStandard h F).symm νN) := by
  let e := (canonicalLowerToStandardHomeomorph F h).symm
  have he : Measurable e := e.continuous.measurable
  have : νN.Regular := hνN.regular
  refine ⟨(Measure.map_ne_zero_iff he.aemeasurable).2 hνN.nonzero,
    Measure.Regular.map e, ?_, ?_, ?_⟩
  · intro g
    refine ⟨(rightTranslate _ g).continuous.measurable, ?_⟩
    change Measure.map (rightTranslate (lowerBlockUnipotent h F) g)
      (Measure.map e νN) = Measure.map e νN
    rw [Measure.map_map (rightTranslate _ g).continuous.measurable he]
    have hcomp : rightTranslate (lowerBlockUnipotent h F) g ∘ e =
        e ∘ rightTranslate (upperUnipotent (t + 1) F) g := by
      funext q
      exact (lowerToStandard_symm_rightTranslate h F g q).symm
    rw [hcomp, ← Measure.map_map he (rightTranslate _ g).continuous.measurable,
      (hνN.right_invariant g).map_eq]
  · intro f hf hfc
    change Integrable _ (Measure.map e νN)
    apply (integrable_map_equiv (μ := νN) e.toMeasurableEquiv
      (quotientAverage (lowerBlockUnipotent h F) (lowerHaar F h) f)).2
    change Integrable (fun q =>
      quotientAverage (lowerBlockUnipotent h F) (lowerHaar F h) f
        ((lowerToStandard h F).symm q)) νN
    simp_rw [quotientAverage_lower_transport]
    exact hνN.averaging_integrable _
      (hf.comp (continuous_const.mul continuous_id))
      (hfc.comp_homeomorph (Homeomorph.mulLeft (blockRotation h F)⁻¹))
  · intro f hf hfc
    change (∫ q, quotientAverage _ _ f q ∂Measure.map e νN) = _
    erw [integral_map_equiv (μ := νN) e.toMeasurableEquiv
      (quotientAverage (lowerBlockUnipotent h F) (lowerHaar F h) f)]
    change (∫ q,
      quotientAverage (lowerBlockUnipotent h F) (lowerHaar F h) f
        ((lowerToStandard h F).symm q) ∂νN) = _
    simp_rw [quotientAverage_lower_transport]
    rw [hνN.integral_formula (fun x => f ((blockRotation h F)⁻¹ * x))
      (hf.comp (continuous_const.mul continuous_id))
      (hfc.comp_homeomorph (Homeomorph.mulLeft (blockRotation h F)⁻¹)),
      integral_mul_left_eq_self]

/-- All compatible standard measures and their prescribed lower transports are sigma-finite. -/
theorem lowerMeasure_sigmaFinite
    (νN : Measure (LeftUnipotentQuotient t F))
    (hνN : IsCompatible (upperUnipotent (t + 1) F)
      (generalLinearHaar F t) (unipotentHaar F t) νN) :
    SigmaFinite νN ∧ SigmaFinite (Measure.map (lowerToStandard h F).symm νN) := by
  have : νN.Regular := hνN.regular
  have : T2Space (LeftUnipotentQuotient t F) :=
    leftQuotient_t2Space _ (UpperUnipotent.isClosed (R := F))
  have : LocallyCompactSpace (LeftUnipotentQuotient t F) :=
    leftQuotient_locallyCompactSpace _
  have : SecondCountableTopology (LeftUnipotentQuotient t F) :=
    Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
  have : SigmaFinite νN := inferInstance
  exact ⟨inferInstance, (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv.sigmaFinite_map⟩

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
