import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.Whittaker.Iwasawa
import Langlands.Analysis.Local.QuotientTopology
import Langlands.LocalField.Normalization.Proof
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Normalized quotient Iwasawa integration

This proposition states the measure identity underlying JPSS Theorem 2.7,
printed p391, equation (3). It uses ordinary diagonal entries and the published
mass-one Haar normalizations. It does not prove the integration formula.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration

universe uF

/-- Every compatible measure on the actual left-unipotent quotient is the
pushforward of diagonal Haar times the restricted compact Haar, weighted by
the inverse upper-Borel modulus. No integrability hypothesis is imposed. -/
def QuotientIwasawaIntegrationStatement {p : ℕ} [Fact p.Prime]
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
  let A := Fin (n + 1) → F.Carrierˣ
  let da : Measure A := Measure.pi (fun _ : Fin (n + 1) =>
    localMultiplicativeHaar F.Carrier)
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let dk := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let δ : A → ℝ := fun a =>
    ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
      T.normalizedAbs ((a i / a j : F.Carrierˣ) : F.Carrier)
  let q : A × Langlands.GeneralLinear (n + 1) F.Carrier →
      LeftUnipotentQuotient n F.Carrier := fun x =>
    leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
      (Iwasawa.diagonalUnits x.1 * x.2)
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      μ = Measure.map q
        ((da.prod dk).withDensity (fun x => ENNReal.ofReal ((δ x.1)⁻¹)))

end Langlands.RankinSelberg
