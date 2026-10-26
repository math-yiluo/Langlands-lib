import Langlands.CategoryTheory.EquivariantDiagram

/-! # Functors and natural transformations on varying-group equivariant diagrams -/

universe uG uI vI uC vC uE vE

namespace Langlands.EquivariantDiagram

open CategoryTheory

variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{uG}}
variable {C : Type uC} [Category.{vC} C]
variable {E : Type uE} [Category.{vE} E]

/-- Apply a functor to the objects, actions, transitions, and morphisms. -/
def mapFunctor (F : C ⥤ E) :
    EquivariantDiagram D C ⥤ EquivariantDiagram D E where
  obj M :=
    { obj := M.obj ⋙ F
      ρ i := (F.mapEnd (M.obj.obj i)).comp (M.ρ i)
      comm f g := by
        change F.map (M.ρ _ g) ≫ F.map (M.obj.map f) =
          F.map (M.obj.map f) ≫ F.map (M.ρ _ ((D.map f).hom g))
        rw [← F.map_comp, M.comm, F.map_comp] }
  map {M N} c :=
    { hom := Functor.whiskerRight c.hom F
      comm i g := by
        change F.map (M.ρ i g) ≫ F.map (c.hom.app i) =
          F.map (c.hom.app i) ≫ F.map (N.ρ i g)
        rw [← F.map_comp, c.comm, F.map_comp] }
  map_id M := by
    apply Hom.ext
    apply NatTrans.ext
    funext i
    exact F.map_id _
  map_comp c d := by
    apply Hom.ext
    apply NatTrans.ext
    funext i
    exact F.map_comp _ _

/-- The component at each object of a natural transformation is equivariant. -/
def mapNatTrans {F F' : C ⥤ E} (α : F ⟶ F') :
    mapFunctor (D := D) F ⟶ mapFunctor (D := D) F' where
  app M :=
    { hom := Functor.whiskerLeft M.obj α
      comm i g := α.naturality (M.ρ i g) }
  naturality {M N} c := by
    apply Hom.ext
    apply NatTrans.ext
    funext i
    exact α.naturality (c.hom.app i)

/-- Postcomposition is itself functorial in the coefficient functor. -/
def postcompose :
    (C ⥤ E) ⥤ (EquivariantDiagram D C ⥤ EquivariantDiagram D E) where
  obj F := mapFunctor F
  map α := mapNatTrans α
  map_id F := by
    apply NatTrans.ext
    funext M
    apply Hom.ext
    rfl
  map_comp α β := by
    apply NatTrans.ext
    funext M
    apply Hom.ext
    rfl

@[simp] theorem mapFunctor_obj_action (F : C ⥤ E)
    (M : EquivariantDiagram D C) (i : I) :
    ((mapFunctor F).obj M).action i = (F.mapAction (D.obj i)).obj (M.action i) := rfl

@[simp] theorem mapFunctor_obj_transition_hom (F : C ⥤ E)
    (M : EquivariantDiagram D C) {i j : I} (f : i ⟶ j) :
    (((mapFunctor F).obj M).transition f).hom = F.map (M.transition f).hom := rfl

@[simp] theorem mapNatTrans_app_hom_app {F F' : C ⥤ E} (α : F ⟶ F')
    (M : EquivariantDiagram D C) (i : I) :
    ((mapNatTrans α).app M).hom.app i = α.app (M.obj.obj i) := rfl

end Langlands.EquivariantDiagram
