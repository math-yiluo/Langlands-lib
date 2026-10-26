import Mathlib.CategoryTheory.Action.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-! # Equivariant diagrams over a varying group diagram -/

universe uG uI vI uC vC uJ vJ

namespace Langlands

open CategoryTheory

/-- A diagram with an action of the group at each index, whose transition maps
are equivariant along the corresponding group homomorphisms. -/
structure EquivariantDiagram {I : Type uI} [Category.{vI} I]
    (D : I ⥤ GrpCat.{uG}) (C : Type uC) [Category.{vC} C] where
  obj : I ⥤ C
  ρ : ∀ i, D.obj i →* End (obj.obj i)
  comm : ∀ {i j} (f : i ⟶ j) (g : D.obj i),
    ρ i g ≫ obj.map f = obj.map f ≫ ρ j ((D.map f).hom g)

namespace EquivariantDiagram

variable {I : Type uI} [Category.{vI} I] {D : I ⥤ GrpCat.{uG}}
variable {C : Type uC} [Category.{vC} C]

/-- Morphisms are natural transformations equivariant at every index. -/
@[ext]
structure Hom (F E : EquivariantDiagram D C) where
  hom : F.obj ⟶ E.obj
  comm : ∀ i (g : D.obj i),
    F.ρ i g ≫ hom.app i = hom.app i ≫ E.ρ i g

instance : Category (EquivariantDiagram D C) where
  Hom F E := Hom F E
  id F :=
    { hom := 𝟙 F.obj
      comm := by intro i g; simp }
  comp f h :=
    { hom := f.hom ≫ h.hom
      comm := by
        intro i g
        change _ ≫ (f.hom.app i ≫ h.hom.app i) =
          (f.hom.app i ≫ h.hom.app i) ≫ _
        rw [← Category.assoc, f.comm, Category.assoc, h.comm, Category.assoc] }
  id_comp f := by apply Hom.ext; exact Category.id_comp f.hom
  comp_id f := by apply Hom.ext; exact Category.comp_id f.hom
  assoc f h k := by apply Hom.ext; exact Category.assoc f.hom h.hom k.hom

/-- Forget the actions, retaining the complete underlying diagram. -/
def forget : EquivariantDiagram D C ⥤ (I ⥤ C) where
  obj F := F.obj
  map f := f.hom

instance : (forget (D := D) (C := C)).Faithful where
  map_injective h := Hom.ext h

/-- The action at one index. -/
def action (F : EquivariantDiagram D C) (i : I) : Action C (D.obj i) where
  V := F.obj.obj i
  ρ := F.ρ i

/-- A transition as a morphism equivariant for the source group. -/
def transition (F : EquivariantDiagram D C) {i j : I} (f : i ⟶ j) :
    F.action i ⟶ (Action.res C (D.map f).hom).obj (F.action j) where
  hom := F.obj.map f
  comm := F.comm f

/-- Evaluate an equivariant diagram and its morphisms at an index. -/
def evaluation (i : I) : EquivariantDiagram D C ⥤ Action C (D.obj i) where
  obj F := F.action i
  map f :=
    { hom := f.hom.app i
      comm := f.comm i }
  map_id F := by apply Action.Hom.ext; rfl
  map_comp f h := by apply Action.Hom.ext; rfl

/-- Reindex the objects, actions, and transition equivariance together. -/
def reindex {J : Type uJ} [Category.{vJ} J] (E : J ⥤ I)
    (F : EquivariantDiagram D C) : EquivariantDiagram (E ⋙ D) C where
  obj := E ⋙ F.obj
  ρ j := F.ρ (E.obj j)
  comm f g := F.comm (E.map f) g

end EquivariantDiagram

end Langlands
