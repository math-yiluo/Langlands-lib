import Langlands.ClassFieldTheory.Local.FiniteArtinSystemStatement

/-! # Uniqueness target for coherent geometric finite Artin systems -/

namespace Langlands.LocalClassField

universe u

/-- The uniqueness conclusion of the full geometric finite Artin-system
assertion, retaining the supplied topology and the entire relation. -/
def GeometricFiniteArtinSystemUniqueness : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData),
    letI := T.topology
    ∀ (a₁ a₂ : FiniteArtinFamily F.Carrier),
      GeometricFiniteArtinSystemRelation F T a₁ →
      GeometricFiniteArtinSystemRelation F T a₂ → a₁ = a₂

end Langlands.LocalClassField
