import Langlands.CategoryTheory.RenardFiniteType

/-!
# Noetherianity and finite type of all subobjects

The equivalence in Renard A.I.3, printed page 249 / PDF page 255, under
the standing existence of arbitrary subobject unions. This file only
declares the proposition; its proof is a separate obligation.
-/

universe u v

open CategoryTheory

namespace Langlands.Renard

/-- With arbitrary subobject unions available, an object is Noetherian
exactly when every one of its subobjects is of finite type. -/
def NoetherianSubobjectFiniteTypeStatement (C : Type u) [Category.{v} C] : Prop :=
  HasAllSubobjectUnions C →
    ∀ X : C, Langlands.Renard.IsNoetherianObject X ↔
      ∀ P : CategoryTheory.Subobject X, Langlands.Renard.IsFiniteTypeObject (P : C)

end Langlands.Renard
