import Langlands.Analysis.Local.CompactQuotientPeriod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.Basic

noncomputable section

universe uG uH

namespace Langlands.QuotientIntegration

open MeasureTheory Set
open Langlands.Global

/-- Actual normalized quotient periods preserve almost-everywhere equality of
specified strongly measurable quotient representatives. -/
def QuotientPeriodAEEqStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) (hΓ : IsDiscrete (Γ : Set G))
    [BorelSpace (LeftCosetSpace Γ)]
    (μ : Measure G) [μ.IsHaarMeasure]
    {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    (Λ : Subgroup H) (hΛ : IsDiscrete (Λ : Set H))
    [BorelSpace (LeftCosetSpace Λ)]
    (μH : Measure H) [IsFiniteMeasureOnCompacts μH]
    (j : H →* G) (_hj : Continuous j) (hjΛ : ∀ η : Λ, j η ∈ Γ)
    (χ : H →* ℂˣ) (_hχ : Continuous χ) (hχΛ : ∀ η : Λ, χ η = 1)
    (φ ψ : LeftCosetSpace Γ → ℂ) (_hφ : StronglyMeasurable φ)
    (_hψ : StronglyMeasurable ψ)
    (_heq : φ =ᵐ[LeftCosetSpace.discreteQuotientMeasure Γ hΓ μ] ψ),
    let νH := LeftCosetSpace.normalizedMeasure Λ μH
      (LeftCosetSpace.fundamentalDomain Λ hΛ)
    ∀ᵐ g ∂μ,
      (periodIntegrand Γ Λ j hjΛ χ hχΛ φ g =ᵐ[νH]
        periodIntegrand Γ Λ j hjΛ χ hχΛ ψ g) ∧
      (HasConvergentQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ νH φ g ↔
        HasConvergentQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ νH ψ g) ∧
      normalizedQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ hΛ μH φ g =
        normalizedQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ hΛ μH ψ g

end Langlands.QuotientIntegration
