import Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationStatement
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory GeneralLinear QuotientIntegration
open scoped BigOperators

universe uF

/-- Conditional transport of the actual quotient measure and its integrals to
cumulative-product root coordinates with the inverse-modulus weight. -/
def QuotientRootIntegrationStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  QuotientIwasawaIntegrationStatement F T n →
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
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F.Carrier)
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let κ := (generalLinearHaar F.Carrier n).restrict (K : Set _)
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let q : A × Langlands.GeneralLinear (n + 1) F.Carrier →
      LeftUnipotentQuotient n F.Carrier := fun x =>
    leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
      (Iwasawa.diagonalUnits (d x.1) * x.2)
  let ρ : A → ℝ := fun a =>
    (∏ i, T.normalizedAbs (a i : F.Carrier) ^ ((i.val + 1) * (n - i.val)))⁻¹
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F.Carrier) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      μ = Measure.map q ((dA.prod κ).withDensity (fun x => ENNReal.ofReal (ρ x.1))) ∧
      ∀ f : LeftUnipotentQuotient n F.Carrier → ℂ, Measurable f →
        let H := fun a z => f (q (a, z)) * w a
        (Integrable f μ ↔ (∫⁻ a, ∫⁻ z, ‖H a z‖ₑ ∂κ ∂dA) < ⊤) ∧
        (Integrable f μ → (∫ x, f x ∂μ) = ∫ a, ∫ z, H a z ∂κ ∂dA)

end Langlands.RankinSelberg
