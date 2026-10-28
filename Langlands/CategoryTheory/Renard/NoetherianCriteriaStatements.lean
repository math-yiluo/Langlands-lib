import Langlands.CategoryTheory.RenardFiniteType
import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Renard's Noetherian-object criteria

Statement targets for Appendix A.I.3, printed page 248 / PDF254.
The comparison with Mathlib is an internal source-correspondence target.
-/

set_option autoImplicit false

universe u v

open CategoryTheory

namespace Langlands.Renard

/-- The source maximal-subset definition agrees with Mathlib's
co-well-foundedness of the actual categorical subobject order. -/
def NoetherianMathlibComparisonStatement
    (C : Type u) [Category.{v} C] : Prop :=
  ∀ X : C,
    Langlands.Renard.IsNoetherianObject X ↔
      CategoryTheory.IsNoetherianObject X

/-- Source Noetherianity is equivalent to the existence of maximal members
in all nonempty chains of actual categorical subobjects. -/
def NoetherianChainMaximalityStatement
    (C : Type u) [Category.{v} C] : Prop :=
  ∀ X : C,
    Langlands.Renard.IsNoetherianObject X ↔
      ∀ S : Set (Subobject X), S.Nonempty → IsChain (· ≤ ·) S →
        ∃ P ∈ S, ∀ Q ∈ S, P ≤ Q → Q = P

/-- Source Noetherianity is equivalent to eventual stabilization of every
monotone natural-number sequence of actual categorical subobjects. -/
def NoetherianSequenceStabilizationStatement
    (C : Type u) [Category.{v} C] : Prop :=
  ∀ X : C,
    Langlands.Renard.IsNoetherianObject X ↔
      ∀ f : ℕ → Subobject X, Monotone f →
        ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m

/-- The Mathlib, nonempty-chain and increasing-sequence comparisons, in that
order, with independent object and Hom universes. -/
def NoetherianCriteriaStatement
    (C : Type u) [Category.{v} C] : Prop :=
  NoetherianMathlibComparisonStatement C ∧
    NoetherianChainMaximalityStatement C ∧
      NoetherianSequenceStabilizationStatement C

end Langlands.Renard
