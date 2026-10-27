import Langlands.AlgebraicGeometry.Picard.RigidifiedRepresentationUniversalBundleStatement

/-! # Universal rigidified bundles from representations of the class presheaf: proof -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle

/-- A representation of the actual class presheaf is induced by an actual universal
rigidified line bundle: any representative of the class corresponding to `𝟙 P`. -/
theorem representationUniversalBundle : RepresentationUniversalBundleStatement.{u} := by
  intro S X f ε section_eq coherence P r
  obtain ⟨L, hL⟩ := Quotient.exists_rep (r.homEquiv (𝟙 P))
  have key : ∀ (T : Over S) (h : T ⟶ P),
      classifyingMap f ε section_eq L T h = r.homEquiv h := by
    intro T h
    have h1 : r.homEquiv h =
        (classPresheaf coherence f ε section_eq).map h.op (r.homEquiv (𝟙 P)) := by
      simpa using r.homEquiv_comp h (𝟙 P)
    rw [h1, ← hL]
    rfl
  refine ⟨L, fun T ↦ ?_, key⟩
  have e : classifyingMap f ε section_eq L T = r.homEquiv := funext (key T)
  rw [e]
  exact r.homEquiv.bijective

end Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle
