import Langlands.Representation.RankinSelberg.CanonicalCharacterChange

/-! # Canonical analytic measures for the intermediate-tail parameters -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear QuotientIntegration MeasureTheory HarmonicAnalysis TopologicalSpace

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Every supplied additive Haar measure is sigma finite for the given
p-adic realization. No self-duality or scalar normalization is required. -/
theorem scalarHaar_sigmaFinite :
    letI := T.topology
    letI := borel F.Carrier
    ∀ η : AdditiveHaarMeasure F.Carrier, SigmaFinite η.measure := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.sigmaCompactSpace
  let := borel F.Carrier
  intro η
  infer_instance

/-- The actual rectangular product of the supplied scalar Haar measure,
bundled as a regular additive Haar measure without renormalization. -/
def rectangularAdditiveHaarMeasure (j t : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier →
      AdditiveHaarMeasure (Matrix (Fin j) (Fin t) F.Carrier) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let := T.sigmaCompactSpace
  let := T.pseudoMetrizableSpace
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro η
  let : SigmaFinite η.measure := scalarHaar_sigmaFinite T η
  let : (rectangularMeasure η j t).IsAddHaarMeasure := inferInstance
  have : SigmaCompactSpace (Matrix (Fin j) (Fin t) F.Carrier) :=
    inferInstanceAs (SigmaCompactSpace (Fin j → Fin t → F.Carrier))
  have : PseudoMetrizableSpace (Matrix (Fin j) (Fin t) F.Carrier) :=
    inferInstanceAs (PseudoMetrizableSpace (Fin j → Fin t → F.Carrier))
  have : BorelSpace (Matrix (Fin j) (Fin t) F.Carrier) :=
    inferInstanceAs (BorelSpace (Fin j → Fin t → F.Carrier))
  have : LocallyCompactSpace (Matrix (Fin j) (Fin t) F.Carrier) :=
    inferInstanceAs (LocallyCompactSpace (Fin j → Fin t → F.Carrier))
  have : IsLocallyFiniteMeasure (rectangularMeasure η j t) := inferInstance
  exact ⟨rectangularMeasure η j t, inferInstance,
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _⟩

@[simp]
theorem rectangularAdditiveHaarMeasure_measure (j t : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    ∀ η : AdditiveHaarMeasure F.Carrier,
      (rectangularAdditiveHaarMeasure T j t η).measure = rectangularMeasure η j t := by
  let := T.topology
  let := borel F.Carrier
  intro η
  rfl

/-- The given scalar normalization supplies all parameter-measure hypotheses
used in localization, including rectangular spaces with an empty index. -/
theorem rectangularMeasure_analytic_properties (j t : ℕ) :
    letI := T.topology
    letI := borel F.Carrier
    ∀ η : AdditiveHaarMeasure F.Carrier,
      SigmaFinite (rectangularMeasure η j t) ∧
      (rectangularMeasure η j t).Regular ∧
      (rectangularMeasure η j t).IsAddHaarMeasure ∧
      (rectangularMeasure η j t).IsOpenPosMeasure ∧
      IsFiniteMeasureOnCompacts (rectangularMeasure η j t) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  intro η
  let : SigmaFinite η.measure := scalarHaar_sigmaFinite T η
  let h := rectangularAdditiveHaarMeasure T j t η
  let : (rectangularMeasure η j t).IsAddHaarMeasure := h.isAddHaar
  have hreg : (rectangularMeasure η j t).Regular := h.regular
  exact ⟨inferInstance, hreg, inferInstance, inferInstance, inferInstance⟩

/-- Every quotient measure compatible with the specified normalized Haar
inputs is sigma finite; the caller's measure is retained exactly. -/
theorem compatible_quotientMeasure_sigmaFinite (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      SigmaFinite μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro μ hμ
  rw [unipotentQuotientHaar_unique F.Carrier n μ hμ]
  exact unipotentQuotientHaar_sigmaFinite_normalized T n

end Langlands.RankinSelberg.InducedTailIntermediate
