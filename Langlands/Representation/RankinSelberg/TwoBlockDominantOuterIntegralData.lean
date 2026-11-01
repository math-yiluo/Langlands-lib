import Langlands.Representation.RankinSelberg.TwoBlockLowerFixedSliceMeasureTransport

/-!
# Outer integrals for the strictly dominant rectangle kernel

This helper retains arbitrary functions on the actual lower quotient. It uses
exactly the existing lower transport of each supplied standard quotient measure.
The actual rectangle-integrated kernel, norm profile and fiber predicate are
supplied by `TwoBlockDominantQuotientKernelData`.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockDominantRectangular

open MeasureTheory GeneralLinear QuotientIntegration TwoBlockLowerUnipotentQuotient

universe uF uE

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance outerFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance outerFieldValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance outerLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance outerFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance outerFieldSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance outerGeneralLinearGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup n
local instance outerGeneralLinearLocallyCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace n
local instance outerGeneralLinearSecondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology n

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
variable [MeasurableSpace (LeftUnipotentQuotient t F.Carrier)]
  [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
variable [MeasurableSpace (LowerQuotient h F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)]

omit [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)] in
/-- The lower measure is exactly this map of the supplied standard measure. -/
theorem lowerQuotientMeasure_eq_map
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) :
    TwoBlockLowerFixedSlice.lowerMeasure F h νN =
      Measure.map (lowerToStandard h F.Carrier).symm νN := rfl

/-- Total Bochner integration transports along the actual quotient equivalence,
without any integrability assumption. -/
theorem integral_lowerQuotientMeasure
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (K : LowerQuotient h F.Carrier → E) :
    (∫ q, K q ∂TwoBlockLowerFixedSlice.lowerMeasure F h νN) =
      ∫ q, K ((lowerToStandard h F.Carrier).symm q) ∂νN :=
  integral_map_equiv (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv K

/-- Absolute integrability also transports in both directions, independently of
any identity of totalized integral values. -/
theorem integrable_lowerQuotientMeasure_iff
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (K : LowerQuotient h F.Carrier → E) :
    Integrable K (TwoBlockLowerFixedSlice.lowerMeasure F h νN) ↔
      Integrable (fun q => K ((lowerToStandard h F.Carrier).symm q)) νN :=
  integrable_map_equiv (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv K

/-- Almost-everywhere fiber conditions transport for arbitrary predicates. -/
theorem ae_lowerQuotientMeasure_iff
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (P : LowerQuotient h F.Carrier → Prop) :
    (∀ᵐ q ∂TwoBlockLowerFixedSlice.lowerMeasure F h νN, P q) ↔
      ∀ᵐ q ∂νN, P ((lowerToStandard h F.Carrier).symm q) :=
  (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv.measurableEmbedding.ae_map_iff

/-- The outer complex integral against the exact lower measure. -/
def outerIntegral (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (K : LowerQuotient h F.Carrier → ℂ) : ℂ :=
  ∫ q, K q ∂TwoBlockLowerFixedSlice.lowerMeasure F h νN

omit [BorelSpace (LeftUnipotentQuotient t F.Carrier)]
  [BorelSpace (LowerQuotient h F.Carrier)] in
/-- Evaluation against the explicitly prescribed map measure. -/
theorem outerIntegral_eq (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (K : LowerQuotient h F.Carrier → ℂ) :
    outerIntegral F h νN K =
      ∫ q, K q ∂Measure.map (lowerToStandard h F.Carrier).symm νN := rfl

/-- Evaluation on the standard quotient, with no representative selection. -/
theorem outerIntegral_standard (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (K : LowerQuotient h F.Carrier → ℂ) :
    outerIntegral F h νN K =
      ∫ q, K ((lowerToStandard h F.Carrier).symm q) ∂νN :=
  integral_lowerQuotientMeasure F h νN K

/-- Actual outer complex integrability, recorded as a condition, not inferred. -/
def OuterIntegrable (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (K : LowerQuotient h F.Carrier → ℂ) : Prop :=
  Integrable K (TwoBlockLowerFixedSlice.lowerMeasure F h νN)

/-- Outer integrability of the supplied real norm profile. -/
def NormProfileIntegrable (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (N : LowerQuotient h F.Carrier → ℝ) : Prop :=
  Integrable N (TwoBlockLowerFixedSlice.lowerMeasure F h νN)

/-- Conditions for an analytic successor: actual outer complex integrability,
outer integrability of the real norm profile, and almost-everywhere actual fiber
integrability. No clause is inferred from a totalized integral value. -/
def AbsoluteInput (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (K : LowerQuotient h F.Carrier → ℂ) (N : LowerQuotient h F.Carrier → ℝ)
    (P : LowerQuotient h F.Carrier → Prop) : Prop :=
  OuterIntegrable F h νN K ∧ NormProfileIntegrable F h νN N ∧
    ∀ᵐ q ∂TwoBlockLowerFixedSlice.lowerMeasure F h νN, P q

/-- The full absolute-input condition written on the standard quotient. -/
theorem absoluteInput_standard_iff
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (K : LowerQuotient h F.Carrier → ℂ) (N : LowerQuotient h F.Carrier → ℝ)
    (P : LowerQuotient h F.Carrier → Prop) :
    AbsoluteInput F h νN K N P ↔
      Integrable (fun q => K ((lowerToStandard h F.Carrier).symm q)) νN ∧
      Integrable (fun q => N ((lowerToStandard h F.Carrier).symm q)) νN ∧
      ∀ᵐ q ∂νN, P ((lowerToStandard h F.Carrier).symm q) := by
  unfold AbsoluteInput OuterIntegrable NormProfileIntegrable
  rw [integrable_lowerQuotientMeasure_iff, integrable_lowerQuotientMeasure_iff,
    ae_lowerQuotientMeasure_iff]

section Compatible

variable [MeasurableSpace (GeneralLinear (t + 1) F.Carrier)]
  [BorelSpace (GeneralLinear (t + 1) F.Carrier)]
variable [MeasurableSpace (upperUnipotent (t + 1) F.Carrier)]
  [BorelSpace (upperUnipotent (t + 1) F.Carrier)]

/-- Compatibility for every supplied right-invariance certificate and every
standard quotient measure, at the existing exact standard Haar normalizations. -/
def standardCompatible
    (hN : Measure.IsMulRightInvariant (unipotentHaar F.Carrier t))
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) : Prop :=
  letI := hN
  IsCompatible (upperUnipotent (t + 1) F.Carrier)
    (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN

/-- Every compatible supplied standard measure and its prescribed lower measure
are sigma-finite. This selects no new measure or normalization. -/
theorem standardCompatible_sigmaFinite
    (hN : Measure.IsMulRightInvariant (unipotentHaar F.Carrier t))
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (hνN : standardCompatible F hN νN) :
    SigmaFinite νN ∧ SigmaFinite (TwoBlockLowerFixedSlice.lowerMeasure F h νN) := by
  let := hN
  have : νN.Regular := hνN.regular
  have : T2Space (LeftUnipotentQuotient t F.Carrier) :=
    leftQuotient_t2Space _ (UpperUnipotent.isClosed (R := F.Carrier))
  have : LocallyCompactSpace (LeftUnipotentQuotient t F.Carrier) :=
    leftQuotient_locallyCompactSpace _
  have : SecondCountableTopology (LeftUnipotentQuotient t F.Carrier) :=
    Topology.IsOpenQuotientMap.secondCountableTopology (leftQuotient_isOpenQuotientMap _)
  have hσ : SigmaFinite νN := inferInstance
  exact ⟨hσ, (canonicalLowerToStandardHomeomorph F h).symm.toMeasurableEquiv.sigmaFinite_map⟩

end Compatible

end Langlands.RankinSelberg.TwoBlockDominantRectangular
