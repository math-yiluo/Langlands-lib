import Langlands.CategoryTheory.Renard.AdjointRepresentabilityStatements
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Renard A.V.1: proofs of representability and uniqueness of adjoints

The representability criterion constructs an actual right adjoint from
objectwise representation data. Uniqueness is witnessed by natural isomorphisms.
-/

open CategoryTheory

namespace Langlands.Renard.AdjointRepresentability

universe vA uA vB uB

/-- Objectwise representability of the Hom presheaves characterizes right adjoints. -/
theorem rightAdjointRepresentability :
    RightAdjointRepresentabilityStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G
  constructor
  · rintro ⟨F, ⟨adj⟩⟩ X
    exact Functor.rightAdjointObjIsDefined_of_adjunction adj X
  · intro h
    have : G.IsLeftAdjoint := by
      rw [Functor.isLeftAdjoint_iff_rightAdjointObjIsDefined_eq_top]
      ext X
      simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
      exact h X
    exact ⟨G.rightAdjoint, ⟨Adjunction.ofIsLeftAdjoint G⟩⟩

/-- Any two right adjoints of an actual functor are naturally isomorphic. -/
theorem rightAdjointUniqueness :
    RightAdjointUniquenessStatement.{vA, uA, vB, uB} := by
  intro A _ B _ G F F' adj adj'
  exact ⟨adj.rightAdjointUniq adj'⟩

/-- Any two left adjoints of an actual functor are naturally isomorphic. -/
theorem leftAdjointUniqueness :
    LeftAdjointUniquenessStatement.{vA, uA, vB, uB} := by
  intro A _ B _ F G G' adj adj'
  exact ⟨adj.leftAdjointUniq adj'⟩

/-- Renard's representability criterion and both uniqueness assertions. -/
theorem adjointRepresentability :
    AdjointRepresentabilityStatements.{vA, uA, vB, uB} :=
  ⟨rightAdjointRepresentability, rightAdjointUniqueness, leftAdjointUniqueness⟩

end Langlands.Renard.AdjointRepresentability
