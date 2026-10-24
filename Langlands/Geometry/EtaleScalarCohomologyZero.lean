import Langlands.Geometry.EtaleScalarDiagram

/-!
# Scalar restriction in degree-zero etale cohomology
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)
variable (X : Scheme.{u})

/-- Transport the canonical scalar section comparison to degree-zero cohomology. -/
def scalarRestrictionCohomologyZeroIso :
    sheafRestrictScalars φ X ⋙ EtaleDerivedSections.cohomology X R 0 ≅
      EtaleDerivedSections.cohomology X A 0 ⋙ ModuleCat.restrictScalars.{u} φ :=
  Functor.isoWhiskerLeft (sheafRestrictScalars φ X)
      (EtaleDerivedSections.cohomologyZeroIso X R) ≪≫
    scalarRestrictionSectionsIso φ ≪≫
    Functor.isoWhiskerRight (EtaleDerivedSections.cohomologyZeroIso X A).symm
      (ModuleCat.restrictScalars.{u} φ)

/-- The degree-zero comparison commutes with the canonical identification with sections. -/
theorem scalarRestrictionCohomologyZero_sections
    (F : EtaleDerivedSections.ModuleSheaf X A) :
    (scalarRestrictionCohomologyZeroIso φ X).hom.app F ≫
        (ModuleCat.restrictScalars φ).map
          ((EtaleDerivedSections.cohomologyZeroIso X A).hom.app F) =
      (EtaleDerivedSections.cohomologyZeroIso X R).hom.app
          ((sheafRestrictScalars φ X).obj F) ≫
        (scalarRestrictionSectionsIso φ).hom.app F := by
  dsimp [scalarRestrictionCohomologyZeroIso]
  simp only [Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  rfl

variable {X} {G : Type t} [Group G] (ρ : G →* (Aut X)ᵐᵒᵖ)

/-- Scalar restriction commutes with degree-zero geometric cohomology actions. -/
def scalarRestrictionCohomologyZeroFunctorIso :
    scalarRestrictionFunctor φ ρ ⋙ pullbackCohomologyFunctor R ρ 0 ≅
      pullbackCohomologyFunctor A ρ 0 ⋙ (ModuleCat.restrictScalars.{u} φ).mapAction G :=
  Functor.isoWhiskerLeft (scalarRestrictionFunctor φ ρ)
      (pullbackCohomologyZeroFunctorIso R ρ) ≪≫
    scalarRestrictionSectionsFunctorIso φ ρ ≪≫
    Functor.isoWhiskerRight (pullbackCohomologyZeroFunctorIso A ρ).symm
      ((ModuleCat.restrictScalars.{u} φ).mapAction G)

/-- The equivariant degree-zero scalar comparison commutes with ordinary section actions. -/
theorem scalarRestrictionCohomologyZeroFunctor_sections (F : EquivariantSheaf A ρ) :
    (scalarRestrictionCohomologyZeroFunctorIso φ ρ).hom.app F ≫
        ((ModuleCat.restrictScalars φ).mapAction G).map
          ((pullbackCohomologyZeroFunctorIso A ρ).hom.app F) =
      (pullbackCohomologyZeroFunctorIso R ρ).hom.app
          ((scalarRestrictionFunctor φ ρ).obj F) ≫
        (scalarRestrictionSectionsFunctorIso φ ρ).hom.app F := by
  dsimp [scalarRestrictionCohomologyZeroFunctorIso]
  simp only [Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  rfl

variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}

namespace EquivariantCoefficientDiagram

/-- Scalar restriction commutes naturally with the degree-zero cohomology action diagram. -/
def restrictScalarsCohomologyZeroFunctorIso :
    restrictScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) φ ⋙ cohomologyFunctor 0 ≅
      cohomologyFunctor 0 ⋙
        (Functor.whiskeringRight J (Action (ModuleCat.{u} A) G)
          (Action (ModuleCat.{u} R) G)).obj
            ((ModuleCat.restrictScalars.{u} φ).mapAction G) :=
  Functor.isoWhiskerLeft (restrictScalarsFunctor φ) cohomologyZeroFunctorIso ≪≫
    restrictScalarsSectionsFunctorIso φ ≪≫
    Functor.isoWhiskerRight cohomologyZeroFunctorIso.symm
      ((Functor.whiskeringRight J (Action (ModuleCat.{u} A) G)
        (Action (ModuleCat.{u} R) G)).obj
          ((ModuleCat.restrictScalars.{u} φ).mapAction G))

/-- Evaluation recovers the scalar comparison on the vertex's geometric cohomology action. -/
@[simp] theorem restrictScalarsCohomologyZeroFunctorIso_hom_app_app
    (D : EquivariantCoefficientDiagram A S ρ hρ) (i : J) :
    ((restrictScalarsCohomologyZeroFunctorIso φ).hom.app D).app i =
      (scalarRestrictionCohomologyZeroFunctorIso φ (ρ i)).hom.app (D.obj i) := rfl

/-- Inverse evaluation recovers the inverse scalar comparison at the vertex. -/
@[simp] theorem restrictScalarsCohomologyZeroFunctorIso_inv_app_app
    (D : EquivariantCoefficientDiagram A S ρ hρ) (i : J) :
    ((restrictScalarsCohomologyZeroFunctorIso φ).inv.app D).app i =
      (scalarRestrictionCohomologyZeroFunctorIso φ (ρ i)).inv.app (D.obj i) := rfl

/-- The diagram comparison commutes with the canonical degree-zero section identification. -/
theorem restrictScalarsCohomologyZero_sections
    (D : EquivariantCoefficientDiagram A S ρ hρ) :
    (restrictScalarsCohomologyZeroFunctorIso φ).hom.app D ≫
        Functor.whiskerRight (cohomologyZeroIso D).hom
          ((ModuleCat.restrictScalars φ).mapAction G) =
      (cohomologyZeroIso (restrictScalars φ D)).hom ≫
        (restrictScalarsSectionsIso φ D).hom := by
  apply NatTrans.ext
  funext i
  exact scalarRestrictionCohomologyZeroFunctor_sections φ (ρ i) (D.obj i)

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
