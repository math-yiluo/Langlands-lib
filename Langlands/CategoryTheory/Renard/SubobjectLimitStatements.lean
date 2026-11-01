import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Renard A.IV: subobject intersections and unions

Statement-only interpretations of A.IV.1 example 6 and its A.IV.2 dual in
the actual category of subobjects of a fixed object. The order bounds are
the intersections and unions defined in A.I.2. No existence is assumed.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard.SubobjectLimit

universe vC uC uI

/-- A cone on a family of subobjects is limiting exactly when its vertex is
the greatest lower bound in the existing categorical subobject order. -/
def IntersectionLimitStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] (X : C)
    (I : Type uI) (F : I → Subobject X)
    (t : Cone (Discrete.functor F)),
    Nonempty (IsLimit t) ↔ IsGLB (Set.range F) t.pt

/-- A cocone on a family of subobjects is colimiting exactly when its vertex
is the least upper bound in the existing categorical subobject order. -/
def UnionColimitStatement : Prop :=
  ∀ (C : Type uC) [Category.{vC} C] (X : C)
    (I : Type uI) (F : I → Subobject X)
    (t : Cocone (Discrete.functor F)),
    Nonempty (IsColimit t) ↔ IsLUB (Set.range F) t.pt

/-- The subobject intersection interpretation followed by its union dual. -/
def SubobjectLimitStatements : Prop :=
  IntersectionLimitStatement.{vC, uC, uI} ∧
    UnionColimitStatement.{vC, uC, uI}

end Langlands.Renard.SubobjectLimit
