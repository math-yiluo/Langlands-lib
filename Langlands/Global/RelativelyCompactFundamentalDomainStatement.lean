import Langlands.Global.LeftCosetFundamentalDomain
import Mathlib.Topology.Separation.Regular

noncomputable section

universe u

open MeasureTheory Set Topology

namespace Langlands.Global.LeftCosetSpace

/-- A compact set meeting every orbit yields a relatively compact Borel transversal
which computes the existing quotient measure for every invariant ambient measure. -/
def RelativelyCompactFundamentalDomainStatement : Prop :=
  ∀ {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
    (K : Set H) (_hK : IsCompact K)
    (_hcover : ∀ x : H, ∃ γ : Γ, (γ : H) * x ∈ K),
    ∃ s : Set H, MeasurableSet s ∧ IsCompact (closure s) ∧
      (∀ x : H, ∃! γ : Γ, (γ : H) * x ∈ s) ∧
      (∀ ν : Measure H, IsFundamentalDomain Γ s ν) ∧
      (∀ (ν : Measure H) [SMulInvariantMeasure Γ H ν],
        MeasurePreserving (mk Γ) (ν.restrict s) (discreteQuotientMeasure Γ hΓ ν)) ∧
      (∀ (ν : Measure H) [IsFiniteMeasureOnCompacts ν], ν s < ⊤) ∧
      (∀ (ν : Measure H) [SMulInvariantMeasure Γ H ν] [IsFiniteMeasureOnCompacts ν],
        ν ≠ 0 → IsProbabilityMeasure (normalizedMeasure Γ ν s) ∧
          normalizedMeasure Γ ν s = normalizedMeasure Γ ν (fundamentalDomain Γ hΓ))

end Langlands.Global.LeftCosetSpace
