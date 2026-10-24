import Langlands.Geometry.EtaleScalarDiagram
import Langlands.Geometry.EtaleEquivariantCoefficientRestriction

/-!
# Scalar restriction, group restriction and reindexing
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t t' v' w'

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
variable {G : Type t} [Group G] {H : Type t'} [Group H] (ψ : H →* G)

section Sheaves

variable {X : Scheme.{u}} (ρ : G →* (Aut X)ᵐᵒᵖ)

/-- Restricting coefficient scalars commutes with restricting the acting group. -/
def scalarRestrictionGroupIso :
    scalarRestrictionFunctor φ ρ ⋙ restrictionFunctor R ρ ψ ≅
      restrictionFunctor A ρ ψ ⋙ scalarRestrictionFunctor φ (ρ.comp ψ) :=
  Iso.refl _

/-- The group/scalar interchange has identity underlying sheaf map. -/
@[simp] theorem scalarRestrictionGroupIso_hom_app_hom (F : EquivariantSheaf A ρ) :
    ((scalarRestrictionGroupIso φ ψ ρ).hom.app F).hom =
      𝟙 ((sheafRestrictScalars φ X).obj F.obj) := rfl

/-- The inverse group/scalar interchange has identity underlying sheaf map. -/
@[simp] theorem scalarRestrictionGroupIso_inv_app_hom (F : EquivariantSheaf A ρ) :
    ((scalarRestrictionGroupIso φ ψ ρ).inv.app F).hom =
      𝟙 ((sheafRestrictScalars φ X).obj F.obj) := rfl

/-- The canonical section comparisons commute with group and scalar restriction. -/
theorem scalarRestrictionGroup_sections (F : EquivariantSheaf A ρ) :
    (restrictionSectionsFunctorIso R ρ ψ).hom.app
        ((scalarRestrictionFunctor φ ρ).obj F) ≫
      (Action.res (ModuleCat.{u} R) ψ).map
        ((scalarRestrictionSectionsFunctorIso φ ρ).hom.app F) =
    (pullbackSectionsFunctor R (ρ.comp ψ)).map
        ((scalarRestrictionGroupIso φ ψ ρ).hom.app F) ≫
      (scalarRestrictionSectionsFunctorIso φ (ρ.comp ψ)).hom.app
        ((restrictionFunctor A ρ ψ).obj F) ≫
      ((ModuleCat.restrictScalars.{u} φ).mapAction H).map
        ((restrictionSectionsFunctorIso A ρ ψ).hom.app F) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, restrictionSectionsFunctorIso_hom_app_hom,
    Action.res_map_hom, pullbackSectionsFunctor_map_hom,
    scalarRestrictionGroupIso_hom_app_hom, Functor.mapAction_map_hom]
  erw [(EtaleDerivedSections.sections X R).map_id,
    (ModuleCat.restrictScalars.{u} φ).map_id]
  simp only [Category.id_comp]
  rfl

end Sheaves

variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}

namespace EquivariantCoefficientDiagram

/-- Scalar and group restriction commute on compatible coefficient diagrams. -/
def restrictScalarsGroupIso :
    restrictScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) φ ⋙ restrictGroupFunctor ψ ≅
      restrictGroupFunctor ψ ⋙ restrictScalarsFunctor φ :=
  Iso.refl _

/-- At every vertex the diagram interchange is the sheaf interchange. -/
@[simp] theorem restrictScalarsGroupIso_hom_app_app
    (D : EquivariantCoefficientDiagram A S ρ hρ) (i : J) :
    ((restrictScalarsGroupIso φ ψ).hom.app D).app i =
      (scalarRestrictionGroupIso φ ψ (ρ i)).hom.app (D.obj i) := rfl

/-- The inverse diagram interchange is the inverse sheaf interchange. -/
@[simp] theorem restrictScalarsGroupIso_inv_app_app
    (D : EquivariantCoefficientDiagram A S ρ hρ) (i : J) :
    ((restrictScalarsGroupIso φ ψ).inv.app D).app i =
      (scalarRestrictionGroupIso φ ψ (ρ i)).inv.app (D.obj i) := rfl

/-- The diagram section comparisons commute with scalar and group restriction. -/
theorem restrictScalarsGroup_sections (D : EquivariantCoefficientDiagram A S ρ hρ) :
    (restrictGroupSectionsIso ψ (restrictScalars φ D)).hom ≫
      Functor.whiskerRight (restrictScalarsSectionsIso φ D).hom
        (Action.res (ModuleCat.{u} R) ψ) =
    sectionsFunctor.map ((restrictScalarsGroupIso φ ψ).hom.app D) ≫
      (restrictScalarsSectionsIso φ (restrictGroup ψ D)).hom ≫
      Functor.whiskerRight (restrictGroupSectionsIso ψ D).hom
        ((ModuleCat.restrictScalars.{u} φ).mapAction H) := by
  apply NatTrans.ext
  funext i
  exact scalarRestrictionGroup_sections φ ψ (ρ i) (D.obj i)

variable {I : Type v'} [Category.{w'} I] (F : I ⥤ J)

/-- Changing the index category commutes with coefficient scalar restriction. -/
def reindexRestrictScalarsIso :
    reindexFunctor (R := A) (S := S) (ρ := ρ) (hρ := hρ) F ⋙
        restrictScalarsFunctor φ ≅
      restrictScalarsFunctor φ ⋙ reindexFunctor F :=
  Iso.refl _

/-- Reindexing the scalar section comparison selects its original component. -/
theorem reindex_restrictScalarsSectionsIso_hom_app
    (D : EquivariantCoefficientDiagram A S ρ hρ) (i : I) :
    (restrictScalarsSectionsIso φ (reindex F D)).hom.app i =
      (restrictScalarsSectionsIso φ D).hom.app (F.obj i) := rfl

/-- Reindexing also preserves the inverse scalar section comparison. -/
theorem reindex_restrictScalarsSectionsIso_inv_app
    (D : EquivariantCoefficientDiagram A S ρ hρ) (i : I) :
    (restrictScalarsSectionsIso φ (reindex F D)).inv.app i =
      (restrictScalarsSectionsIso φ D).inv.app (F.obj i) := rfl

/-- The section comparison for reindexed coefficients is its precomposition. -/
theorem reindex_restrictScalarsSectionsIso_hom
    (D : EquivariantCoefficientDiagram A S ρ hρ) :
    (restrictScalarsSectionsIso φ (reindex F D)).hom =
      Functor.whiskerLeft F (restrictScalarsSectionsIso φ D).hom := rfl

/-- The inverse section comparison for reindexed coefficients is its precomposition. -/
theorem reindex_restrictScalarsSectionsIso_inv
    (D : EquivariantCoefficientDiagram A S ρ hρ) :
    (restrictScalarsSectionsIso φ (reindex F D)).inv =
      Functor.whiskerLeft F (restrictScalarsSectionsIso φ D).inv := rfl

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
