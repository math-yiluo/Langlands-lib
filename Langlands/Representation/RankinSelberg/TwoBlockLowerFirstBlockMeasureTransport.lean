import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport

/-!
# The prescribed lower-unipotent Haar and compatible quotient transport

Subgroup elements are transported by inverse conjugation. Quotient classes are
transported by inverse left multiplication by the block rotation.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open MeasureTheory GeneralLinear QuotientIntegration TwoBlockLowerUnipotentQuotient

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local instance lowerMeasureTransportInstance01 : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance lowerMeasureTransportInstance02 : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance lowerMeasureTransportInstance03 : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance lowerMeasureTransportInstance04 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance lowerMeasureTransportInstance05 : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance lowerMeasureTransportInstance06 : MeasurableSpace F.Carrier := borel _
local instance lowerMeasureTransportInstance07 : BorelSpace F.Carrier := ⟨rfl⟩
local instance lowerMeasureTransportInstance08 (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance lowerMeasureTransportInstance09 (n : ℕ) : MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance lowerMeasureTransportInstance10 (n : ℕ) : BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩
local instance lowerMeasureTransportInstance11 (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n
local instance lowerMeasureTransportInstance12 (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance lowerMeasureTransportInstance13 (n : ℕ) : MeasurableSpace (upperUnipotent n F.Carrier) := borel _
local instance lowerMeasureTransportInstance14 (n : ℕ) : BorelSpace (upperUnipotent n F.Carrier) := ⟨rfl⟩
local instance lowerMeasureTransportInstance15 (n : ℕ) : SecondCountableTopology (upperUnipotent n F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerMeasureTransportInstance16 (n : ℕ) : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
  UpperUnipotent.locallyCompactSpace
local instance lowerMeasureTransportInstance17 : MeasurableSpace (lowerBlockUnipotent h F.Carrier) := borel _
local instance lowerMeasureTransportInstance18 : BorelSpace (lowerBlockUnipotent h F.Carrier) := ⟨rfl⟩
local instance lowerMeasureTransportInstance19 : SecondCountableTopology (lowerBlockUnipotent h F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance lowerMeasureTransportInstance20 : LocallyCompactSpace (lowerBlockUnipotent h F.Carrier) :=
  (isClosed_lowerBlockUnipotent_canonical F h).locallyCompactSpace

/-- Exactly the prescribed inverse-conjugation transport of the standard Haar. -/
def lowerHaar : Measure (lowerBlockUnipotent h F.Carrier) :=
  Measure.map (conjugationEquiv h F.Carrier).symm (unipotentHaar F.Carrier t)

instance lowerHaar_isHaar : (lowerHaar F h).IsHaarMeasure :=
  (canonicalConjugationHomeomorph F h).symm.isHaarMeasure_map _

instance lowerHaar_regular : (lowerHaar F h).Regular :=
  Measure.Regular.map (canonicalConjugationHomeomorph F h).symm.toHomeomorph

instance lowerHaar_isMulRightInvariant : (lowerHaar F h).IsMulRightInvariant := by
  let e := (canonicalConjugationHomeomorph F h).symm
  let μ := unipotentHaar F.Carrier t
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

local instance lowerMeasureTransportInstance21 : MeasurableSpace (LeftUnipotentQuotient t F.Carrier) := borel _
local instance lowerMeasureTransportInstance22 : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
local instance lowerMeasureTransportInstance23 : MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance lowerMeasureTransportInstance24 : BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩

/-- Exact orbital-average transport through the two different prescribed maps. -/
theorem quotientAverage_lower_transport (f : GeneralLinear (t + 1) F.Carrier → ℂ)
    (q : LeftUnipotentQuotient t F.Carrier) :
    quotientAverage (lowerBlockUnipotent h F.Carrier) (lowerHaar F h) f
        ((lowerToStandard h F.Carrier).symm q) =
      quotientAverage (upperUnipotent (t + 1) F.Carrier) (unipotentHaar F.Carrier t)
        (fun x => f ((blockRotation h F.Carrier)⁻¹ * x)) q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [lowerToStandard_symm_mk, quotientAverage_mk, quotientAverage_mk, lowerHaar]
    erw [integral_map_equiv (μ := unipotentHaar F.Carrier t)
      (canonicalConjugationHomeomorph F h).symm.toHomeomorph.toMeasurableEquiv
      (fun a => f (a.val * ((blockRotation h F.Carrier)⁻¹ * g)))]
    apply integral_congr_ae
    filter_upwards [] with n
    congr 1
    change ((blockRotation h F.Carrier)⁻¹ * n.val * blockRotation h F.Carrier) *
      ((blockRotation h F.Carrier)⁻¹ * g) = (blockRotation h F.Carrier)⁻¹ * (n.val * g)
    group

/-- Every compatible standard quotient measure has the required compatible
inverse-left-translation transport, with exactly the inverse-conjugation Haar. -/
theorem lowerMeasure_isCompatible
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (hνN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN) :
    IsCompatible (lowerBlockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (lowerHaar F h)
      (Measure.map (lowerToStandard h F.Carrier).symm νN) := by
  let e := (canonicalLowerToStandardHomeomorph F h).symm
  have he : Measurable e := e.continuous.measurable
  have : νN.Regular := hνN.regular
  refine ⟨(Measure.map_ne_zero_iff he.aemeasurable).2 hνN.nonzero,
    Measure.Regular.map e, ?_, ?_, ?_⟩
  · intro g
    refine ⟨(rightTranslate _ g).continuous.measurable, ?_⟩
    change Measure.map (rightTranslate (lowerBlockUnipotent h F.Carrier) g)
      (Measure.map e νN) = Measure.map e νN
    rw [Measure.map_map (rightTranslate _ g).continuous.measurable he]
    have hcomp : rightTranslate (lowerBlockUnipotent h F.Carrier) g ∘ e =
        e ∘ rightTranslate (upperUnipotent (t + 1) F.Carrier) g := by
      funext q
      exact (lowerToStandard_symm_rightTranslate h F.Carrier g q).symm
    rw [hcomp, ← Measure.map_map he (rightTranslate _ g).continuous.measurable,
      (hνN.right_invariant g).map_eq]
  · intro f hf hfc
    change Integrable _ (Measure.map e νN)
    apply (integrable_map_equiv (μ := νN) e.toMeasurableEquiv
      (quotientAverage (lowerBlockUnipotent h F.Carrier) (lowerHaar F h) f)).2
    change Integrable (fun q =>
      quotientAverage (lowerBlockUnipotent h F.Carrier) (lowerHaar F h) f
        ((lowerToStandard h F.Carrier).symm q)) νN
    simp_rw [quotientAverage_lower_transport]
    exact hνN.averaging_integrable _
      (hf.comp (continuous_const.mul continuous_id))
      (hfc.comp_homeomorph (Homeomorph.mulLeft (blockRotation h F.Carrier)⁻¹))
  · intro f hf hfc
    change (∫ q, quotientAverage _ _ f q ∂Measure.map e νN) = _
    erw [integral_map_equiv (μ := νN) e.toMeasurableEquiv
      (quotientAverage (lowerBlockUnipotent h F.Carrier) (lowerHaar F h) f)]
    change (∫ q,
      quotientAverage (lowerBlockUnipotent h F.Carrier) (lowerHaar F h) f
        ((lowerToStandard h F.Carrier).symm q) ∂νN) = _
    simp_rw [quotientAverage_lower_transport]
    rw [hνN.integral_formula (fun x => f ((blockRotation h F.Carrier)⁻¹ * x))
      (hf.comp (continuous_const.mul continuous_id))
      (hfc.comp_homeomorph (Homeomorph.mulLeft (blockRotation h F.Carrier)⁻¹)),
      integral_mul_left_eq_self]

/-- All compatible standard measures and their prescribed lower transports are sigma-finite. -/
theorem lowerMeasure_sigmaFinite
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (hνN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN) :
    SigmaFinite νN ∧ SigmaFinite (Measure.map (lowerToStandard h F.Carrier).symm νN) := by
  have : νN.Regular := hνN.regular
  have : T2Space (LeftUnipotentQuotient t F.Carrier) :=
    leftQuotient_t2Space _ (UpperUnipotent.isClosed (R := F.Carrier))
  have : LocallyCompactSpace (LeftUnipotentQuotient t F.Carrier) :=
    leftQuotient_locallyCompactSpace _
  have : SecondCountableTopology (LeftUnipotentQuotient t F.Carrier) :=
    Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
  have : SigmaFinite νN := inferInstance
  exact ⟨inferInstance, (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv.sigmaFinite_map⟩

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
