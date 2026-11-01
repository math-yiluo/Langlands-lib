import Langlands.Geometry.EtaleDerivedEquivariantMap
import Langlands.Geometry.EtalePullbackGroupRestriction

/-! # Group restriction of actual derived etale actions -/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u w w' wX wY wT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X R)]
  [HasDerivedCategory.{wT} (ModuleCat.{u} R)]
variable {G : Type w} [Group G] {H : Type w'} [Group H]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (φ : H →* G)

/-- Restricting the coefficient action evaluates the derived action at the
image of each group element. -/
theorem restriction_derivedSections_ρ (F : EquivariantSheaf R ρ) (h : H) :
    ((pullbackDerivedSectionsFunctor R (ρ.comp φ)).obj
        ((restrictionFunctor R ρ φ).obj F)).ρ h =
      ((pullbackDerivedSectionsFunctor R ρ).obj F).ρ (φ h) := by
  rw [pullbackDerivedSectionsFunctor_obj_ρ, pullbackDerivedSectionsFunctor_obj_ρ]
  rfl

/-- Group restriction identifies the same derived-section object with its
restricted action. -/
def restrictionDerivedSectionsIso (F : EquivariantSheaf R ρ) :
    (pullbackDerivedSectionsFunctor R (ρ.comp φ)).obj
        ((restrictionFunctor R ρ φ).obj F) ≅
      (Action.res (DerivedCategory.Plus (ModuleCat.{u} R)) φ).obj
        ((pullbackDerivedSectionsFunctor R ρ).obj F) :=
  Action.mkIso (Iso.refl ((EtaleDerivedSectionsPlus.derivedSections X R).obj F.obj))
    (fun h => by
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [Category.comp_id, Category.id_comp]
      exact restriction_derivedSections_ρ R ρ φ F h)

/-- Derived sections commute naturally with group restriction. -/
def restrictionDerivedSectionsFunctorIso :
    restrictionFunctor R ρ φ ⋙ pullbackDerivedSectionsFunctor R (ρ.comp φ) ≅
      pullbackDerivedSectionsFunctor R ρ ⋙
        Action.res (DerivedCategory.Plus (ModuleCat.{u} R)) φ :=
  NatIso.ofComponents (fun F => restrictionDerivedSectionsIso R ρ φ F)
    (fun {F E} α => by
      apply Action.Hom.ext
      change (EtaleDerivedSectionsPlus.derivedSections X R).map α.hom ≫ 𝟙 _ =
        𝟙 _ ≫ (EtaleDerivedSectionsPlus.derivedSections X R).map α.hom
      rw [Category.comp_id, Category.id_comp])

/-- The restriction comparison is the identity on the actual derived object. -/
@[simp] theorem restrictionDerivedSectionsFunctorIso_hom_app_hom
    (F : EquivariantSheaf R ρ) :
    ((restrictionDerivedSectionsFunctorIso R ρ φ).hom.app F).hom =
      𝟙 ((EtaleDerivedSectionsPlus.derivedSections X R).obj F.obj) := rfl

/-- The inverse restriction comparison is also the identity underneath. -/
@[simp] theorem restrictionDerivedSectionsFunctorIso_inv_app_hom
    (F : EquivariantSheaf R ρ) :
    ((restrictionDerivedSectionsFunctorIso R ρ φ).inv.app F).hom =
      𝟙 ((EtaleDerivedSectionsPlus.derivedSections X R).obj F.obj) := rfl

/-- Restriction commutes with canonical recovery of ordinary cohomology. -/
theorem restriction_derivedHomology (F : EquivariantSheaf R ρ) (q : ℕ) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction H).map
        ((restrictionDerivedSectionsFunctorIso R ρ φ).hom.app F) ≫
        (Action.res (ModuleCat.{u} R) φ).map
          ((pullbackDerivedHomologyFunctorIso R ρ q).hom.app F) =
      (pullbackDerivedHomologyFunctorIso R (ρ.comp φ) q).hom.app
          ((restrictionFunctor R ρ φ).obj F) ≫
        (restrictionCohomologyFunctorIso R ρ φ q).hom.app F := by
  apply Action.Hom.ext
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map (𝟙 _) ≫
      (EtaleDerivedSectionsPlus.homologyNatIso X R q).hom.app F.obj =
    (EtaleDerivedSectionsPlus.homologyNatIso X R q).hom.app F.obj ≫ 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- Restriction commutes with canonical degree-zero recovery of sections. -/
theorem restriction_derivedZero (F : EquivariantSheaf R ρ) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction H).map
        ((restrictionDerivedSectionsFunctorIso R ρ φ).hom.app F) ≫
        (Action.res (ModuleCat.{u} R) φ).map
          ((pullbackDerivedZeroFunctorIso R ρ).hom.app F) =
      (pullbackDerivedZeroFunctorIso R (ρ.comp φ)).hom.app
          ((restrictionFunctor R ρ φ).obj F) ≫
        (restrictionSectionsFunctorIso R ρ φ).hom.app F := by
  apply Action.Hom.ext
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
      (𝟙 ((EtaleDerivedSectionsPlus.derivedSections X R).obj F.obj)) ≫
      (EtaleDerivedSectionsPlus.homologyZeroIso X R).hom.app F.obj =
    (EtaleDerivedSectionsPlus.homologyZeroIso X R).hom.app F.obj ≫ 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

variable [HasDerivedCategory.{wY} (EtaleDerivedSections.ModuleSheaf Y R)]
variable (τ : G →* (Aut Y)ᵐᵒᵖ) (f : Y ⟶ X) [Etale f]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)

namespace GeometricCoefficientMap

variable {R ρ τ f hf} {F : EquivariantSheaf R ρ} {E : EquivariantSheaf R τ}

/-- Restricting a geometric coefficient map commutes with its actual derived map. -/
theorem restrictGroup_derivedSectionsMap
    (α : GeometricCoefficientMap R ρ τ f hf F E) :
    (α.restrictGroup φ).derivedSectionsMap ≫
        (restrictionDerivedSectionsFunctorIso R τ φ).hom.app E =
      (restrictionDerivedSectionsFunctorIso R ρ φ).hom.app F ≫
        (Action.res (DerivedCategory.Plus (ModuleCat.{u} R)) φ).map
          α.derivedSectionsMap := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, derivedSectionsMap_hom,
    restrictionDerivedSectionsFunctorIso_hom_app_hom, Action.res_map_hom,
    restrictGroup_hom]
  change derivedSectionsMapWithCoefficients f R α.hom ≫ 𝟙 _ =
    𝟙 _ ≫ derivedSectionsMapWithCoefficients f R α.hom
  rw [Category.comp_id, Category.id_comp]

end GeometricCoefficientMap

/-- Derived geometric pullback commutes with group restriction through the
canonical sheaf-level interchange comparison. -/
theorem restrictionPullback_derivedSections (F : EquivariantSheaf R ρ) :
    (equivariantPullbackDerivedSections R (ρ.comp φ) (τ.comp φ) f
        (fun h => hf (φ h))).app ((restrictionFunctor R ρ φ).obj F) ≫
      (pullbackDerivedSectionsFunctor R (τ.comp φ)).map
        ((restrictionPullbackIso R ρ τ f hf φ).hom.app F) ≫
      (restrictionDerivedSectionsFunctorIso R τ φ).hom.app
        ((equivariantPullback R ρ τ f hf).obj F) =
    (restrictionDerivedSectionsFunctorIso R ρ φ).hom.app F ≫
      (Action.res (DerivedCategory.Plus (ModuleCat.{u} R)) φ).map
        ((equivariantPullbackDerivedSections R ρ τ f hf).app F) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, equivariantPullbackDerivedSections_app_hom,
    pullbackDerivedSectionsFunctor_map_hom, restrictionPullbackIso_hom_app_hom,
    restrictionDerivedSectionsFunctorIso_hom_app_hom, Action.res_map_hom]
  change (EtalePullback.derivedSectionsMap f R).app F.obj ≫
      (EtaleDerivedSectionsPlus.derivedSections Y R).map (𝟙 _) ≫ 𝟙 _ =
    𝟙 _ ≫ (EtalePullback.derivedSectionsMap f R).app F.obj
  erw [(EtaleDerivedSectionsPlus.derivedSections Y R).map_id,
    Category.comp_id, Category.comp_id, Category.id_comp]

end Langlands.Geometry.EtaleCohomologyAction
