import Langlands.Algebra.FiniteFreeRingHom
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.Types.Basic

/-! # Natural finite equations for actions in a ring-valued functor -/

noncomputable section

open CategoryTheory Module
open scoped BigOperators

universe uC vC uI uO uR

namespace Langlands.FiniteFreeRingHom

variable {C : Type uC} [Category.{vC} C]
    {I : Type uI} [Fintype I] {O : Type uO} [Ring O]

/-- Unital actions of the fixed ring, lifted to the common tuple/action universe. -/
def actionFunctor (_b : Basis I ℤ O) (R : C ⥤ RingCat.{uR}) :
    C ⥤ Type (max uI uO uR) where
  obj X := ULift.{max uI uO uR} (O →+* R.obj X)
  map f := TypeCat.ofHom fun a => ⟨(R.map f).hom.comp a.down⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ (fun a => ?_)
    apply ULift.ext
    ext x
    change (R.map (𝟙 X)) (a.down x) = a.down x
    rw [R.map_id]
    rfl
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ (fun a => ?_)
    apply ULift.ext
    ext x
    change (R.map (f ≫ g)) (a.down x) = (R.map g) ((R.map f) (a.down x))
    rw [R.map_comp]
    rfl

variable (b : Basis I ℤ O) (R : C ⥤ RingCat.{uR})

/-- Tuples satisfying the fixed unit and ordered multiplication equations. -/
def solutionsFunctor : C ⥤ Type (max uI uO uR) where
  obj X := ULift.{max uI uO uR} (Solutions b (R.obj X))
  map f := TypeCat.ofHom fun r => ⟨map b (R.map f).hom r.down⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ (fun r => ?_)
    apply ULift.ext
    apply Subtype.ext
    funext i
    change (R.map (𝟙 X)) (r.down.val i) = r.down.val i
    rw [R.map_id]
    rfl
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ (fun r => ?_)
    apply ULift.ext
    apply Subtype.ext
    funext i
    change (R.map (f ≫ g)) (r.down.val i) = (R.map g) ((R.map f) (r.down.val i))
    rw [R.map_comp]
    rfl

/-- The finite-equation equivalence is natural for every morphism of the test category. -/
def actionSolutionsIso : actionFunctor b R ≅ solutionsFunctor b R :=
  NatIso.ofComponents (fun X =>
    ((Equiv.ulift.{max uI uO uR}.trans (equiv b (R := R.obj X))).trans
      Equiv.ulift.{max uI uO uR}.symm).toIso) (by
    intro X Y f
    refine ConcreteCategory.hom_ext _ _ (fun a => ?_)
    apply ULift.ext
    exact equiv_natural b a.down (R.map f).hom)

@[simp] theorem actionSolutionsIso_hom_app_apply (X : C) (a : O →+* R.obj X) (i : I) :
    ((actionSolutionsIso b R).hom.app X ⟨a⟩).down.val i = a (b i) := rfl

@[simp] theorem actionSolutionsIso_inv_app_apply (X : C)
    (r : Solutions b (R.obj X)) (x : O) :
    ((actionSolutionsIso b R).inv.app X ⟨r⟩).down x = ∑ i, b.repr x i • r.val i :=
  ofRelations_apply b r.val r.property x

end Langlands.FiniteFreeRingHom
