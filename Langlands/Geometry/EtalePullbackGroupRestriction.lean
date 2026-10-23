import Langlands.Geometry.EtaleActionRestriction
import Langlands.Geometry.EtaleEquivariantPullback

/-!
# Group restriction and equivariant geometric pullback
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u w w'

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (R : Type u) [CommRing R]
variable {G : Type w} [Group G] {H : Type w'} [Group H]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (τ : G →* (Aut Y)ᵐᵒᵖ)
variable (f : Y ⟶ X) [Etale f]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)
variable (φ : H →* G)

/-- Group restriction commutes with equivariant geometric pullback. -/
def restrictionPullbackIso :
    restrictionFunctor R ρ φ ⋙
        equivariantPullback R (ρ.comp φ) (τ.comp φ) f (fun h => hf (φ h)) ≅
      equivariantPullback R ρ τ f hf ⋙ restrictionFunctor R τ φ :=
  Iso.refl _

/-- The interchange comparison is the identity on the underlying pulled-back sheaf. -/
@[simp] theorem restrictionPullbackIso_hom_app_hom (F : EquivariantSheaf R ρ) :
    ((restrictionPullbackIso R ρ τ f hf φ).hom.app F).hom =
      𝟙 ((restriction f (ModuleCat.{u} R)).obj F.obj) := rfl

/-- The inverse interchange comparison also has identity underlying sheaf map. -/
@[simp] theorem restrictionPullbackIso_inv_app_hom (F : EquivariantSheaf R ρ) :
    ((restrictionPullbackIso R ρ τ f hf φ).inv.app F).hom =
      𝟙 ((restriction f (ModuleCat.{u} R)).obj F.obj) := rfl

namespace GeometricCoefficientMap

variable {R ρ τ f hf} {F : EquivariantSheaf R ρ} {E : EquivariantSheaf R τ}

/-- Restrict both coefficient actions and their geometric compatibility square. -/
def restrictGroup (α : GeometricCoefficientMap R ρ τ f hf F E) :
    GeometricCoefficientMap R (ρ.comp φ) (τ.comp φ) f (fun h => hf (φ h))
      ((restrictionFunctor R ρ φ).obj F) ((restrictionFunctor R τ φ).obj E) where
  hom := α.hom
  comm h := α.comm (φ h)

/-- Group restriction retains the geometric coefficient morphism. -/
@[simp] theorem restrictGroup_hom (α : GeometricCoefficientMap R ρ τ f hf F E) :
    (α.restrictGroup φ).hom = α.hom := rfl

/-- Restriction respects precomposition in the source coefficient sheaf. -/
theorem restrictGroup_precomp {F' : EquivariantSheaf R ρ}
    (α : GeometricCoefficientMap R ρ τ f hf F E) (β : F' ⟶ F) :
    (α.precomp β).restrictGroup φ =
      (α.restrictGroup φ).precomp ((restrictionFunctor R ρ φ).map β) := rfl

/-- Restriction respects postcomposition in the target coefficient sheaf. -/
theorem restrictGroup_postcomp {E' : EquivariantSheaf R τ}
    (α : GeometricCoefficientMap R ρ τ f hf F E) (β : E ⟶ E') :
    (α.postcomp β).restrictGroup φ =
      (α.restrictGroup φ).postcomp ((restrictionFunctor R τ φ).map β) := rfl

/-- The geometric cohomology map commutes with restriction of the acting group. -/
theorem restrictGroup_cohomologyMap
    (α : GeometricCoefficientMap R ρ τ f hf F E) (q : ℕ) :
    (α.restrictGroup φ).cohomologyMap q ≫
        (restrictionCohomologyFunctorIso R τ φ q).hom.app E =
      (restrictionCohomologyFunctorIso R ρ φ q).hom.app F ≫
        (Action.res (ModuleCat.{u} R) φ).map (α.cohomologyMap q) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, cohomologyMap_hom,
    restrictionCohomologyFunctorIso_hom_app_hom, Action.res_map_hom,
    restrictGroup_hom]
  change cohomologyMapWithCoefficients f R q α.hom ≫ 𝟙 _ =
    𝟙 _ ≫ cohomologyMapWithCoefficients f R q α.hom
  rw [Category.comp_id, Category.id_comp]

/-- The geometric section map commutes with restriction of the acting group. -/
theorem restrictGroup_sectionsMap
    (α : GeometricCoefficientMap R ρ τ f hf F E) :
    (α.restrictGroup φ).sectionsMap ≫
        (restrictionSectionsFunctorIso R τ φ).hom.app E =
      (restrictionSectionsFunctorIso R ρ φ).hom.app F ≫
        (Action.res (ModuleCat.{u} R) φ).map α.sectionsMap := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, sectionsMap_hom,
    restrictionSectionsFunctorIso_hom_app_hom, Action.res_map_hom,
    restrictGroup_hom]
  change ((EtalePullback.sectionsMap f R).app F.obj ≫
      (EtaleDerivedSections.sections Y R).map α.hom) ≫ 𝟙 _ =
    𝟙 _ ≫ (EtalePullback.sectionsMap f R).app F.obj ≫
      (EtaleDerivedSections.sections Y R).map α.hom
  rw [Category.comp_id, Category.id_comp]

end GeometricCoefficientMap

/-- Geometric pullback on cohomology commutes with group restriction through
its canonical sheaf interchange comparison. -/
theorem restrictionPullback_cohomology (F : EquivariantSheaf R ρ) (q : ℕ) :
    (equivariantPullbackCohomology R (ρ.comp φ) (τ.comp φ) f
        (fun h => hf (φ h)) q).app ((restrictionFunctor R ρ φ).obj F) ≫
      (pullbackCohomologyFunctor R (τ.comp φ) q).map
        ((restrictionPullbackIso R ρ τ f hf φ).hom.app F) ≫
      (restrictionCohomologyFunctorIso R τ φ q).hom.app
        ((equivariantPullback R ρ τ f hf).obj F) =
    (restrictionCohomologyFunctorIso R ρ φ q).hom.app F ≫
      (Action.res (ModuleCat.{u} R) φ).map
        ((equivariantPullbackCohomology R ρ τ f hf q).app F) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, equivariantPullbackCohomology_app_hom,
    pullbackCohomologyFunctor_map_hom, restrictionPullbackIso_hom_app_hom,
    restrictionCohomologyFunctorIso_hom_app_hom, Action.res_map_hom]
  change (EtalePullback.cohomologyMap f R q).app F.obj ≫
      (EtaleDerivedSections.cohomology Y R q).map (𝟙 _) ≫ 𝟙 _ =
    𝟙 _ ≫ (EtalePullback.cohomologyMap f R q).app F.obj
  erw [(EtaleDerivedSections.cohomology Y R q).map_id,
    Category.comp_id]

/-- Geometric pullback on sections commutes with group restriction through
its canonical sheaf interchange comparison. -/
theorem restrictionPullback_sections (F : EquivariantSheaf R ρ) :
    (equivariantPullbackSections R (ρ.comp φ) (τ.comp φ) f
        (fun h => hf (φ h))).app ((restrictionFunctor R ρ φ).obj F) ≫
      (pullbackSectionsFunctor R (τ.comp φ)).map
        ((restrictionPullbackIso R ρ τ f hf φ).hom.app F) ≫
      (restrictionSectionsFunctorIso R τ φ).hom.app
        ((equivariantPullback R ρ τ f hf).obj F) =
    (restrictionSectionsFunctorIso R ρ φ).hom.app F ≫
      (Action.res (ModuleCat.{u} R) φ).map
        ((equivariantPullbackSections R ρ τ f hf).app F) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, equivariantPullbackSections_app_hom,
    pullbackSectionsFunctor_map_hom, restrictionPullbackIso_hom_app_hom,
    restrictionSectionsFunctorIso_hom_app_hom, Action.res_map_hom]
  change (EtalePullback.sectionsMap f R).app F.obj ≫
      (EtaleDerivedSections.sections Y R).map (𝟙 _) ≫ 𝟙 _ =
    𝟙 _ ≫ (EtalePullback.sectionsMap f R).app F.obj
  erw [(EtaleDerivedSections.sections Y R).map_id,
    Category.comp_id]

end Langlands.Geometry.EtaleCohomologyAction
