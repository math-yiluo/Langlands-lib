import Langlands.CategoryTheory.EquivariantDiagramFunctor

/-! # Identity and composition of functors on varying-group diagrams -/

universe uG uI vI uC vC uE vE uF vF

namespace Langlands.EquivariantDiagram

open CategoryTheory

variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{uG}}
variable {C : Type uC} [Category.{vC} C]
variable {E : Type uE} [Category.{vE} E]
variable {B : Type uF} [Category.{vF} B]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A natural isomorphism acts on the entire varying-group diagram category. -/
def mapFunctorCongr {F F' : C ⥤ E} (e : F ≅ F') :
    mapFunctor (D := D) F ≅ mapFunctor (D := D) F' :=
  (postcompose (D := D)).mapIso e

/-- Applying the identity functor identifies with the original diagram. -/
def mapFunctorId : mapFunctor (D := D) (𝟭 C) ≅ 𝟭 (EquivariantDiagram D C) :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- Mapping a composite identifies with successively mapping both functors. -/
def mapFunctorComp (F : C ⥤ E) (F' : E ⥤ B) :
    mapFunctor (D := D) (F ⋙ F') ≅ mapFunctor F ⋙ mapFunctor F' :=
  NatIso.ofComponents (fun _ => Iso.refl _)

@[simp] theorem mapFunctorCongr_hom_app_hom_app {F F' : C ⥤ E} (e : F ≅ F')
    (M : EquivariantDiagram D C) (i : I) :
    ((mapFunctorCongr e).hom.app M).hom.app i = e.hom.app (M.obj.obj i) := rfl

@[simp] theorem mapFunctorCongr_inv_app_hom_app {F F' : C ⥤ E} (e : F ≅ F')
    (M : EquivariantDiagram D C) (i : I) :
    ((mapFunctorCongr e).inv.app M).hom.app i = e.inv.app (M.obj.obj i) := rfl

@[simp] theorem mapFunctorId_hom_app_hom_app (M : EquivariantDiagram D C) (i : I) :
    ((mapFunctorId (D := D) (C := C)).hom.app M).hom.app i = 𝟙 _ := rfl

@[simp] theorem mapFunctorComp_hom_app_hom_app (F : C ⥤ E) (F' : E ⥤ B)
    (M : EquivariantDiagram D C) (i : I) :
    ((mapFunctorComp F F').hom.app M).hom.app i = 𝟙 _ := rfl

end Langlands.EquivariantDiagram
