import Langlands.Geometry.EtaleScalarCohomologyZero
import Langlands.Geometry.EtaleScalarInterchange

/-!
# Scalar and group restriction in degree-zero etale cohomology
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

/-- Compare degree-zero cohomology after restricting both coefficients and the group. -/
def scalarRestrictionGroupCohomologyZeroFunctorIso :
    scalarRestrictionFunctor φ ρ ⋙ restrictionFunctor R ρ ψ ⋙
        pullbackCohomologyFunctor R (ρ.comp ψ) 0 ≅
      pullbackCohomologyFunctor A ρ 0 ⋙
        (ModuleCat.restrictScalars.{u} φ).mapAction G ⋙ Action.res (ModuleCat.{u} R) ψ :=
  Functor.isoWhiskerLeft (scalarRestrictionFunctor φ ρ)
      (restrictionCohomologyFunctorIso R ρ ψ 0) ≪≫
    (Functor.associator (scalarRestrictionFunctor φ ρ)
      (pullbackCohomologyFunctor R ρ 0) (Action.res (ModuleCat.{u} R) ψ)).symm ≪≫
    Functor.isoWhiskerRight (scalarRestrictionCohomologyZeroFunctorIso φ ρ)
      (Action.res (ModuleCat.{u} R) ψ) ≪≫
    Functor.associator (pullbackCohomologyFunctor A ρ 0)
      ((ModuleCat.restrictScalars.{u} φ).mapAction G) (Action.res (ModuleCat.{u} R) ψ)

/-- The simultaneous comparison is group comparison followed by restricted scalar comparison. -/
theorem scalarRestrictionGroupCohomologyZeroFunctorIso_hom_app
    (F : EquivariantSheaf A ρ) :
    (scalarRestrictionGroupCohomologyZeroFunctorIso φ ψ ρ).hom.app F =
      (restrictionCohomologyFunctorIso R ρ ψ 0).hom.app
          ((scalarRestrictionFunctor φ ρ).obj F) ≫
        (Action.res (ModuleCat.{u} R) ψ).map
          ((scalarRestrictionCohomologyZeroFunctorIso φ ρ).hom.app F) := by
  dsimp [scalarRestrictionGroupCohomologyZeroFunctorIso]
  simp only [Category.comp_id, Category.id_comp]

/-- Canonical degree-zero scalar comparisons commute with restriction of the acting group. -/
theorem scalarRestrictionGroup_cohomologyZero (F : EquivariantSheaf A ρ) :
    (restrictionCohomologyFunctorIso R ρ ψ 0).hom.app
        ((scalarRestrictionFunctor φ ρ).obj F) ≫
      (Action.res (ModuleCat.{u} R) ψ).map
        ((scalarRestrictionCohomologyZeroFunctorIso φ ρ).hom.app F) =
    (pullbackCohomologyFunctor R (ρ.comp ψ) 0).map
        ((scalarRestrictionGroupIso φ ψ ρ).hom.app F) ≫
      (scalarRestrictionCohomologyZeroFunctorIso φ (ρ.comp ψ)).hom.app
        ((restrictionFunctor A ρ ψ).obj F) ≫
      ((ModuleCat.restrictScalars.{u} φ).mapAction H).map
        ((restrictionCohomologyFunctorIso A ρ ψ 0).hom.app F) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, restrictionCohomologyFunctorIso_hom_app_hom,
    Action.res_map_hom, pullbackCohomologyFunctor_map_hom,
    scalarRestrictionGroupIso_hom_app_hom, Functor.mapAction_map_hom]
  erw [(EtaleDerivedSections.cohomology X R 0).map_id,
    (ModuleCat.restrictScalars.{u} φ).map_id]
  erw [Category.id_comp]

end Sheaves

variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]
variable {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}

namespace EquivariantCoefficientDiagram

/-- Simultaneous scalar and group restriction of degree-zero cohomology diagrams. -/
def restrictScalarsGroupCohomologyZeroFunctorIso :
    restrictScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) φ ⋙
        restrictGroupFunctor ψ ⋙ cohomologyFunctor 0 ≅
      cohomologyFunctor 0 ⋙
        (Functor.whiskeringRight J (Action (ModuleCat.{u} A) G)
          (Action (ModuleCat.{u} R) G)).obj
            ((ModuleCat.restrictScalars.{u} φ).mapAction G) ⋙
        (Functor.whiskeringRight J (Action (ModuleCat.{u} R) G)
          (Action (ModuleCat.{u} R) H)).obj (Action.res (ModuleCat.{u} R) ψ) :=
  Functor.isoWhiskerLeft (restrictScalarsFunctor φ)
      (restrictGroupCohomologyFunctorIso ψ 0) ≪≫
    (Functor.associator (restrictScalarsFunctor φ) (cohomologyFunctor 0)
      ((Functor.whiskeringRight J (Action (ModuleCat.{u} R) G)
        (Action (ModuleCat.{u} R) H)).obj (Action.res (ModuleCat.{u} R) ψ))).symm ≪≫
    Functor.isoWhiskerRight (restrictScalarsCohomologyZeroFunctorIso φ)
      ((Functor.whiskeringRight J (Action (ModuleCat.{u} R) G)
        (Action (ModuleCat.{u} R) H)).obj (Action.res (ModuleCat.{u} R) ψ)) ≪≫
    Functor.associator (cohomologyFunctor 0)
      ((Functor.whiskeringRight J (Action (ModuleCat.{u} A) G)
        (Action (ModuleCat.{u} R) G)).obj
          ((ModuleCat.restrictScalars.{u} φ).mapAction G))
      ((Functor.whiskeringRight J (Action (ModuleCat.{u} R) G)
        (Action (ModuleCat.{u} R) H)).obj (Action.res (ModuleCat.{u} R) ψ))

/-- The diagram comparison has the expected composite component. -/
theorem restrictScalarsGroupCohomologyZeroFunctorIso_hom_app
    (D : EquivariantCoefficientDiagram A S ρ hρ) :
    (restrictScalarsGroupCohomologyZeroFunctorIso φ ψ).hom.app D =
      (restrictGroupCohomologyIso ψ (restrictScalars φ D) 0).hom ≫
        Functor.whiskerRight ((restrictScalarsCohomologyZeroFunctorIso φ).hom.app D)
          (Action.res (ModuleCat.{u} R) ψ) := by
  dsimp [restrictScalarsGroupCohomologyZeroFunctorIso]
  simp only [Category.comp_id, Category.id_comp]
  rfl

/-- The simultaneous diagram comparison evaluates to the simultaneous action comparison. -/
theorem restrictScalarsGroupCohomologyZeroFunctorIso_hom_app_app
    (D : EquivariantCoefficientDiagram A S ρ hρ) (i : J) :
    ((restrictScalarsGroupCohomologyZeroFunctorIso φ ψ).hom.app D).app i =
      (scalarRestrictionGroupCohomologyZeroFunctorIso φ ψ (ρ i)).hom.app (D.obj i) := by
  rw [restrictScalarsGroupCohomologyZeroFunctorIso_hom_app,
    scalarRestrictionGroupCohomologyZeroFunctorIso_hom_app]
  rfl

/-- Scalar and group restriction commute on the canonical degree-zero comparison diagram. -/
theorem restrictScalarsGroup_cohomologyZero (D : EquivariantCoefficientDiagram A S ρ hρ) :
    (restrictGroupCohomologyIso ψ (restrictScalars φ D) 0).hom ≫
      Functor.whiskerRight ((restrictScalarsCohomologyZeroFunctorIso φ).hom.app D)
        (Action.res (ModuleCat.{u} R) ψ) =
    (cohomologyFunctor 0).map ((restrictScalarsGroupIso φ ψ).hom.app D) ≫
      (restrictScalarsCohomologyZeroFunctorIso φ).hom.app (restrictGroup ψ D) ≫
      Functor.whiskerRight (restrictGroupCohomologyIso ψ D 0).hom
        ((ModuleCat.restrictScalars.{u} φ).mapAction H) := by
  apply NatTrans.ext
  funext i
  exact scalarRestrictionGroup_cohomologyZero φ ψ (ρ i) (D.obj i)

variable {I : Type v'} [Category.{w'} I] (F : I ⥤ J)

/-- Reindexing selects the original forward degree-zero scalar component. -/
theorem reindex_restrictScalarsCohomologyZeroFunctorIso_hom_app
    (D : EquivariantCoefficientDiagram A S ρ hρ) (i : I) :
    ((restrictScalarsCohomologyZeroFunctorIso φ).hom.app (reindex F D)).app i =
      ((restrictScalarsCohomologyZeroFunctorIso φ).hom.app D).app (F.obj i) := rfl

/-- Reindexing selects the original inverse degree-zero scalar component. -/
theorem reindex_restrictScalarsCohomologyZeroFunctorIso_inv_app
    (D : EquivariantCoefficientDiagram A S ρ hρ) (i : I) :
    ((restrictScalarsCohomologyZeroFunctorIso φ).inv.app (reindex F D)).app i =
      ((restrictScalarsCohomologyZeroFunctorIso φ).inv.app D).app (F.obj i) := rfl

/-- Reindexing the forward comparison is precomposition of that diagram map. -/
theorem reindex_restrictScalarsCohomologyZeroFunctorIso_hom
    (D : EquivariantCoefficientDiagram A S ρ hρ) :
    (restrictScalarsCohomologyZeroFunctorIso φ).hom.app (reindex F D) =
      Functor.whiskerLeft F ((restrictScalarsCohomologyZeroFunctorIso φ).hom.app D) := rfl

/-- Reindexing the inverse comparison is precomposition of that diagram map. -/
theorem reindex_restrictScalarsCohomologyZeroFunctorIso_inv
    (D : EquivariantCoefficientDiagram A S ρ hρ) :
    (restrictScalarsCohomologyZeroFunctorIso φ).inv.app (reindex F D) =
      Functor.whiskerLeft F ((restrictScalarsCohomologyZeroFunctorIso φ).inv.app D) := rfl

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
