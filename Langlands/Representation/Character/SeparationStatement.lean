import Langlands.Representation.Character.Basic
import Mathlib.RepresentationTheory.Irreducible

/-! # Character separation for irreducible admissible representations -/

namespace Langlands

open MeasureTheory

universe uG uV uW

/-- Equality of actual distribution characters is equivalent to genuine
representation equivalence, for irreducible admissibles and a regular Haar measure. -/
def CharacterSeparationStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (W : Type uW) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsAdmissible ρ) (hσ : IsAdmissible σ),
    Representation.IsIrreducible ρ → Representation.IsIrreducible σ →
    (Character.distribution μ ρ hρ = Character.distribution μ σ hσ ↔
      ∃ E : V ≃ₗ[ℂ] W, ∀ g v, E (ρ g v) = σ g (E v))

end Langlands
