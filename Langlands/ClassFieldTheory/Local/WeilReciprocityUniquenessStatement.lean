import Langlands.ClassFieldTheory.Local.WeilReciprocityStatement

/-!
# Uniqueness of geometric local Weil reciprocity

This isolates the uniqueness part of the published existence-and-uniqueness
target, without requiring construction of a reciprocity candidate.
-/

namespace Langlands.LocalClassField

universe u

/-- Any two geometrically normalized candidates for the actual local Weil
reciprocity isomorphism agree, for every field and topological realization. -/
def GeometricWeilReciprocityUniqueness : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
    (e₁ e₂ : WeilReciprocityCandidate T (Weil.Local.localResidueDegree F)),
    GeometricWeilReciprocityRelation F T e₁ →
      GeometricWeilReciprocityRelation F T e₂ → e₁ = e₂

/-- The published existence-and-uniqueness target implies its uniqueness part. -/
theorem geometricWeilReciprocityUniqueness_of_existenceUniqueness
    (h : WeilReciprocityExistenceUniqueness.{u}) :
    GeometricWeilReciprocityUniqueness.{u} := by
  intro p _ F T e₁ e₂ h₁ h₂
  obtain ⟨e, _, he⟩ := h p F T
  exact (he e₁ h₁).trans (he e₂ h₂).symm

end Langlands.LocalClassField
