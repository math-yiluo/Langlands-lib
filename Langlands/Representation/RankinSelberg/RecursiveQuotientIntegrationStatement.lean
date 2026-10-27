import Langlands.Representation.RankinSelberg.RecursiveQuotientCoordinates
import Langlands.Representation.RankinSelberg.WhittakerNormData
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Normalized recursive quotient integration

This proposition states the measure identity underlying JPSS Section 8.3,
printed p449, equation (1), on the actual left-unipotent quotients of ranks
`n + 2` and `n + 1`, with the published mass-one Haar normalizations and the
published recursive coordinates. It does not prove the integration formula.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration

universe uF

/-- Every compatible measure on the rank `n + 2` left-unipotent quotient is the
pushforward, under the actual recursive coordinates `(q, a, k) ↦ [diag(g,1) a k]`,
of a compatible rank `n + 1` quotient measure times multiplicative Haar times
the larger Haar measure restricted to the integral subgroup, weighted by the
inverse absolute determinant of the lower coordinate. No integrability
hypothesis is imposed. -/
def RecursiveQuotientIntegrationStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel F.Carrierˣ
  letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 2) F.Carrier)
  letI : BorelSpace (Langlands.GeneralLinear (n + 2) F.Carrier) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 2) F.Carrier)
  letI : BorelSpace (upperUnipotent (n + 2) F.Carrier) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient (n + 1) F.Carrier)
  letI : BorelSpace (LeftUnipotentQuotient (n + 1) F.Carrier) := ⟨rfl⟩
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer (n + 1)
  let dk : Measure (Langlands.GeneralLinear (n + 2) F.Carrier) :=
    (generalLinearHaar F.Carrier (n + 1)).restrict (K : Set _)
  let dMult : Measure F.Carrierˣ := localMultiplicativeHaar F.Carrier
  let coordinates :
      LeftUnipotentQuotient n F.Carrier × F.Carrierˣ ×
          Langlands.GeneralLinear (n + 2) F.Carrier →
        LeftUnipotentQuotient (n + 1) F.Carrier :=
    recursiveQuotientCoordinates (F := F.Carrier) n
  let weight :
      LeftUnipotentQuotient n F.Carrier × F.Carrierˣ ×
          Langlands.GeneralLinear (n + 2) F.Carrier → ENNReal := fun x =>
    ENNReal.ofReal ((quotientDeterminantAbs (normalizedAbsoluteValue T) n x.1)⁻¹)
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (n + 1))],
  ∀ (μsmall : Measure (LeftUnipotentQuotient n F.Carrier))
    (μlarge : Measure (LeftUnipotentQuotient (n + 1) F.Carrier)),
    IsCompatible (upperUnipotent (n + 1) F.Carrier)
      (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μsmall →
    IsCompatible (upperUnipotent (n + 2) F.Carrier)
      (generalLinearHaar F.Carrier (n + 1)) (unipotentHaar F.Carrier (n + 1)) μlarge →
    μlarge = Measure.map coordinates
      ((μsmall.prod (dMult.prod dk)).withDensity weight)

end Langlands.RankinSelberg
