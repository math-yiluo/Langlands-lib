import Langlands.Weil.Representation.RestrictionInduction

/-!
# Focused finite-index induction and restriction statements

These four proposition definitions separate the clauses of
`Langlands.Weil.RepresentationInductionFiniteness`. They assert no proofs and
leave that aggregate unchanged.
-/

namespace Langlands.Weil

universe uG uV

/-- Finite-index induction has finite-dimensional carrier and the expected rank. -/
def RepresentationInductionDimension : Prop :=
  ∀ (G : Type uG) [Group G] (H : Subgroup G) [H.FiniteIndex]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V),
    FiniteDimensional ℂ (Representation.IndV H.subtype ρ) ∧
    Module.finrank ℂ (Representation.IndV H.subtype ρ) =
      H.index * Module.finrank ℂ V

/-- Finite-index induction preserves and reflects finite whole image. -/
def RepresentationInductionFiniteImage : Prop :=
  ∀ (G : Type uG) [Group G] (H : Subgroup G) [H.FiniteIndex]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V),
    (Set.range (ρ.ind H.subtype)).Finite ↔ (Set.range ρ).Finite

/-- Finite-index induction preserves and reflects semisimplicity. -/
def RepresentationInductionSemisimplicity : Prop :=
  ∀ (G : Type uG) [Group G] (H : Subgroup G) [H.FiniteIndex]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V),
    Representation.IsSemisimpleRepresentation (ρ.ind H.subtype) ↔
      Representation.IsSemisimpleRepresentation ρ

/-- Finite-index restriction preserves and reflects semisimplicity. -/
def RepresentationFiniteIndexRestrictionSemisimplicity : Prop :=
  ∀ (G : Type uG) [Group G] (H : Subgroup G) [H.FiniteIndex]
    (V : Type uV) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (σ : Representation ℂ G V),
    Representation.IsSemisimpleRepresentation (σ.comp H.subtype) ↔
      Representation.IsSemisimpleRepresentation σ

end Langlands.Weil
