import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.Order.Preorder.Chain

/-!
# Renard's finite-type and Noetherian conventions

Source: Renard (9 July 2026), Appendix A.I.2–A.I.3, printed pages 248–249.
All unions use the existing order on categorical subobjects.
-/

universe u v

open CategoryTheory

namespace Langlands.Renard

variable {C : Type u} [Category.{v} C]

/-- Every subset of the actual subobject type, including the empty subset,
has a least upper bound in the categorical subobject order. -/
def HasSubobjectUnions (X : C) : Prop :=
  ∀ S : Set (Subobject X), ∃ U : Subobject X, IsLUB S U

/-- Renard's standing category-wide existence of arbitrary subobject unions. -/
def HasAllSubobjectUnions (C : Type u) [Category.{v} C] : Prop :=
  ∀ X : C, HasSubobjectUnions X

/-- Renard's finite-type condition: unions exist, and a nonempty chain of proper
subobjects cannot have the top subobject as its least upper bound. -/
def IsFiniteTypeObject (X : C) : Prop :=
  HasSubobjectUnions X ∧
    ∀ S : Set (Subobject X), S.Nonempty → IsChain (· ≤ ·) S →
      (∀ P ∈ S, P ≠ ⊤) → ¬ IsLUB S ⊤

/-- The source finite-subcover comparison condition, with unions available.
The finite subcover is allowed to be empty. No chain/cover equivalence is asserted. -/
def HasFiniteSubcoverProperty (X : C) : Prop :=
  HasSubobjectUnions X ∧
    ∀ S : Set (Subobject X), IsLUB S ⊤ →
      ∃ T : Finset (Subobject X),
        (T : Set (Subobject X)) ⊆ S ∧ IsLUB (T : Set (Subobject X)) ⊤

/-- Renard's intrinsic Noetherian-object definition: every nonempty subset of
subobjects has a maximal element. It does not require unions to exist. -/
def IsNoetherianObject (X : C) : Prop :=
  ∀ S : Set (Subobject X), S.Nonempty →
    ∃ P ∈ S, ∀ Q ∈ S, P ≤ Q → Q = P

/-- Renard's Noetherian-category convention, including the standing all-unions
assumption: every finite-type object is Noetherian. -/
def IsNoetherianCategory (C : Type u) [Category.{v} C] : Prop :=
  HasAllSubobjectUnions C ∧
    ∀ X : C, IsFiniteTypeObject X → IsNoetherianObject X

end Langlands.Renard
