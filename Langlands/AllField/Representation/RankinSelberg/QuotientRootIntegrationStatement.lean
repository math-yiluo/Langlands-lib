import Langlands.Representation.RankinSelberg.QuotientRootIntegrationStatement
import Langlands.AllField.Representation.RankinSelberg.QuotientIwasawaIntegrationStatement
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding QuotientIwasawaIntegrationStatement QuotientRootIntegrationStatement
open Langlands.AllField.RankinSelberg

open MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open scoped BigOperators

universe uF

/-- Conditional transport of the actual quotient measure and its integrals to
cumulative-product root coordinates with the inverse-modulus weight. -/
def QuotientRootIntegrationStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  QuotientIwasawaIntegrationStatement F T n →
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  letI := borel Fˣ
  letI : BorelSpace Fˣ := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  let A := Fin (n + 1) → Fˣ
  let dA : Measure A := Measure.pi (fun _ => localMultiplicativeHaar F)
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let κ := (generalLinearHaar F n).restrict (K : Set _)
  let d : A → A := fun a i => ∏ j ∈ Finset.univ.filter (i ≤ ·), a j
  let q : A × Langlands.GeneralLinear (n + 1) F →
      LeftUnipotentQuotient n F := fun x =>
    leftQuotientMap (upperUnipotent (n + 1) F)
      (Iwasawa.diagonalUnits (d x.1) * x.2)
  let ρ : A → ℝ := fun a =>
    (∏ i, T.normalizedAbs (a i : F) ^ ((i.val + 1) * (n - i.val)))⁻¹
  let w : A → ℂ := fun a =>
    (∏ i, (T.normalizedAbs (a i : F) : ℂ) ^
      ((i.val + 1) * (n - i.val)))⁻¹
  ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)],
    ∀ μ : Measure (LeftUnipotentQuotient n F),
      IsCompatible (upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μ →
      μ = Measure.map q ((dA.prod κ).withDensity (fun x => ENNReal.ofReal (ρ x.1))) ∧
      ∀ f : LeftUnipotentQuotient n F → ℂ, Measurable f →
        let H := fun a z => f (q (a, z)) * w a
        (Integrable f μ ↔ (∫⁻ a, ∫⁻ z, ‖H a z‖ₑ ∂κ ∂dA) < ⊤) ∧
        (Integrable f μ → (∫ x, f x ∂μ) = ∫ a, ∫ z, H a z ∂κ ∂dA)

end Langlands.AllField.RankinSelberg
