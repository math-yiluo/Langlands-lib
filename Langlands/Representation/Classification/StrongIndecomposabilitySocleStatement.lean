import Langlands.Representation.Classification.StrongIndecomposability
import Langlands.Representation.Classification.CanonicalConstituents
import Mathlib.RingTheory.Artinian.Module

/-!
# Artinian strong indecomposability and the canonical socle

This proposition states the unique-atom criterion for a nonzero Artinian
representation, its canonical complex and smooth socle consequences, and
transport from restriction along a group homomorphism. The Artinian weakening
of Zelevinsky (1980), §5.4, and the canonical-socle adapters are internal derived
content. This module supplies a statement only.
-/

namespace Langlands.Classification

open scoped MonoidAlgebra

universe uK uG uH uV

/-- The Artinian algebraic criterion and the actual smooth socle it supplies. -/
def StrongIndecomposabilitySocleStatement : Prop :=
  (∀ (k : Type uK) [Field k] (G : Type uG) [Group G]
      (V : Type uV) [AddCommGroup V] [Module k V] [Nontrivial V]
      (ρ : Representation k G V), IsArtinian k[G] ρ.asModule →
      (IsStronglyIndecomposable ρ ↔ ∃! S : Subrepresentation ρ, IsAtom S)) ∧
  (∀ (G : Type uG) [Group G] (V : Type uV)
      [AddCommGroup V] [Module ℂ V] [Nontrivial V]
      (ρ : Representation ℂ G V), IsArtinian ℂ[G] ρ.asModule →
      IsStronglyIndecomposable ρ →
      IsIrreducibleSocle ρ (socleRepresentation ρ)) ∧
  (∀ (G : Type uG) [Group G] [TopologicalSpace G]
      (A : SmoothRep.{0, uG, uV} ℂ G), Nontrivial A →
      IsArtinian ℂ[G] A.representation.asModule →
      IsStronglyIndecomposable A.representation →
      ∃ π : SmoothRep.{0, uG, uV} ℂ G,
        IsIrreducibleSocle A.representation π.representation) ∧
  (∀ (k : Type uK) [Field k] (G : Type uG) [Group G]
      (H : Type uH) [Group H] (V : Type uV) [AddCommGroup V] [Module k V]
      (ρ : Representation k G V) (f : H →* G),
      IsStronglyIndecomposable (ρ.comp f) → IsStronglyIndecomposable ρ)

end Langlands.Classification
