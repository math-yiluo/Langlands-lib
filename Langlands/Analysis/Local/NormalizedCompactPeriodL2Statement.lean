import Langlands.Analysis.Local.CompactQuotientPeriod
import Langlands.Analysis.Local.QuotientMeasure
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.ContinuousMap.CompactlySupported

noncomputable section

universe uG uH

namespace Langlands.QuotientIntegration

open MeasureTheory Set
open Langlands.Global
open scoped CompactlySupported

/-- Actual normalized compact quotient periods of L² vectors converge almost
everywhere, are locally integrable, and have a closed vanishing locus. -/
def NormalizedCompactPeriodL2Statement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure]
    (Γ : Subgroup G) (_hΓ : IsClosed (Γ : Set G))
    [MeasurableSpace Γ] [BorelSpace Γ]
    (μΓ : Measure Γ) [SFinite μΓ] [μΓ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μΓ]
    [MeasurableSpace (LeftQuotient Γ)] [BorelSpace (LeftQuotient Γ)]
    (ν : Measure (LeftQuotient Γ)) [IsFiniteMeasureOnCompacts ν]
    (_hν : IsCompatible Γ μ.inv μΓ ν)
    {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    (Λ : Subgroup H) (hΛ : IsDiscrete (Λ : Set H))
    [BorelSpace (LeftCosetSpace Λ)]
    (μH : Measure H) [SMulInvariantMeasure Λ H μH]
    [IsFiniteMeasureOnCompacts μH] (_hμH : μH ≠ 0)
    (K : Set H) (_hK : IsCompact K)
    (_hcover : ∀ h : H, ∃ η : Λ, (η : H) * h ∈ K)
    (j : H →* G) (_hj : Continuous j) (hjΛ : ∀ η : Λ, j η ∈ Γ)
    (χ : H →* ℂˣ) (_hχ : Continuous χ) (hχΛ : ∀ η : Λ, χ η = 1),
    let νH := LeftCosetSpace.normalizedMeasure Λ μH (LeftCosetSpace.fundamentalDomain Λ hΛ)
    let P := normalizedQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ hΛ μH
    (∀ φ : Lp ℂ 2 ν,
      (∀ᵐ g ∂μ.inv, HasConvergentQuotientCharacterPeriod Γ Λ j hjΛ χ hχΛ νH φ g) ∧
      LocallyIntegrable (P φ) μ.inv) ∧
    (∀ f : C_c(G, ℂ), ∃ ℓ : Lp ℂ 2 ν →L[ℂ] ℂ,
      ∀ φ : Lp ℂ 2 ν,
        Integrable (fun g => star (f g) * P φ g) μ.inv ∧
        ℓ φ = ∫ g, star (f g) * P φ g ∂μ.inv) ∧
    IsClosed {φ : Lp ℂ 2 ν | P φ =ᵐ[μ.inv] 0}

end Langlands.QuotientIntegration
