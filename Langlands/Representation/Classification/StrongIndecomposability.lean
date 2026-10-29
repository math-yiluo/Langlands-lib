import Langlands.Representation.SubrepresentationLattice

/-!
# Strong indecomposability

Zelevinsky (1980), §5.4, calls a representation strongly indecomposable when every
two nonzero submodules have nonzero intersection. This module states that
intersection condition for an arbitrary representation of a group over a field,
using Mathlib's lattice of subrepresentations. No nonzero, finiteness or socle
hypothesis is included: the zero representation satisfies the condition vacuously.
-/

namespace Langlands.Classification

universe uK uG uV

/-- Every two nonbottom subrepresentations of `ρ` have nonbottom intersection. -/
def IsStronglyIndecomposable {k : Type uK} [Field k] {G : Type uG} [Group G]
    {V : Type uV} [AddCommGroup V] [Module k V] (ρ : Representation k G V) : Prop :=
  ∀ S T : Subrepresentation ρ, S ≠ ⊥ → T ≠ ⊥ → S ⊓ T ≠ ⊥

/-- A representation on a zero space is strongly indecomposable, since its only
subrepresentation is `⊥`. -/
theorem IsStronglyIndecomposable.of_subsingleton {k : Type uK} [Field k] {G : Type uG}
    [Group G] {V : Type uV} [AddCommGroup V] [Module k V] [Subsingleton V]
    (ρ : Representation k G V) : IsStronglyIndecomposable ρ := by
  intro S _ hS _
  exact absurd (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)) hS

end Langlands.Classification
