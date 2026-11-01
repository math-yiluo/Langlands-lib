import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.Order.Directed

/-!
# Renard A.IV: inverse and direct systems

Statement-only characterizations of the universal properties in A.IV.1 example 5
and the explicit direct-system paragraph of A.IV.2. The index has the source's
pairwise upper-bound property, with no added nonemptiness hypothesis.
-/

open CategoryTheory CategoryTheory.Limits Opposite

namespace Langlands.Renard.OrderedSystemLimit

universe vC uC uI

/-- An inverse-system cone is limiting exactly when every inequality-compatible
family has a unique factor map to its vertex. -/
def InverseLimitStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C]
    (I : Type uI) [PartialOrder I] [IsDirectedOrder I]
    (D : Iᵒᵖ ⥤ C) (t : Cone D),
    Nonempty (IsLimit t) ↔
      ∀ (Y : C) (q : ∀ i : I, Y ⟶ D.obj (op i)),
        (∀ (i j : I) (h : i ≤ j), q j ≫ D.map (homOfLE h).op = q i) →
          ∃! l : Y ⟶ t.pt, ∀ i : I, l ≫ t.π.app (op i) = q i

/-- A direct-system cocone is colimiting exactly when every
inequality-compatible family has a unique factor map from its vertex. -/
def DirectLimitStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C]
    (I : Type uI) [PartialOrder I] [IsDirectedOrder I]
    (D : I ⥤ C) (t : Cocone D),
    Nonempty (IsColimit t) ↔
      ∀ (Y : C) (q : ∀ i : I, D.obj i ⟶ Y),
        (∀ (i j : I) (h : i ≤ j), D.map (homOfLE h) ≫ q j = q i) →
          ∃! l : t.pt ⟶ Y, ∀ i : I, t.ι.app i ≫ l = q i

/-- The two source-system characterizations, inverse followed by direct. -/
def OrderedSystemLimitStatements : Prop :=
  InverseLimitStatement.{vC, uC, uI} ∧ DirectLimitStatement.{vC, uC, uI}

end Langlands.Renard.OrderedSystemLimit
