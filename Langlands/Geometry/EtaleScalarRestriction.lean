import Langlands.Geometry.EtaleEquivariantPullback
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Scalar restriction of equivariant etale sheaves
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable (X : Scheme.{u})

/-- Restrict scalars on every section module of an actual small-etale sheaf. -/
def sheafRestrictScalars :
    EtaleDerivedSections.ModuleSheaf X S ⥤ EtaleDerivedSections.ModuleSheaf X R :=
  sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u} φ)

instance : (sheafRestrictScalars φ X).Faithful :=
  inferInstanceAs (sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u} φ)).Faithful

variable {X}
variable {G : Type w} [Group G] (ρ : G →* (Aut X)ᵐᵒᵖ)

/-- Translation and restriction of coefficient scalars have identical section data. -/
def scalarRestrictionTranslateIso (g : G) :
    translateBy S ρ g ⋙ sheafRestrictScalars φ X ≅
      sheafRestrictScalars φ X ⋙ translateBy R ρ g :=
  Iso.refl _

/-- Restriction of scalars retains the geometric equivariance of a coefficient sheaf. -/
def scalarRestrictionObj (F : EquivariantSheaf S ρ) : EquivariantSheaf R ρ where
  obj := (sheafRestrictScalars φ X).obj F.obj
  act g := (sheafRestrictScalars φ X).map (F.act g)
  act_one := by
    rw [F.act_one]
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    dsimp [sheafRestrictScalars, data, oneIso, EtaleAutomorphism.translateCongr,
      EtaleAutomorphism.translateId]
    simp only [Functor.map_comp, Category.comp_id]
  act_mul g h := by
    rw [F.act_mul]
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    dsimp [sheafRestrictScalars, data, compIso, EtaleAutomorphism.translateCongr,
      EtaleAutomorphism.translateComp]
    simp only [Functor.map_comp]
    rfl

/-- Scalar restriction is functorial on moving-space equivariant coefficients. -/
def scalarRestrictionFunctor : EquivariantSheaf S ρ ⥤ EquivariantSheaf R ρ where
  obj := scalarRestrictionObj φ ρ
  map α :=
    { hom := (sheafRestrictScalars φ X).map α.hom
      comm g := by
        have h := congrArg (fun β => (sheafRestrictScalars φ X).map β) (α.comm g)
        simp only [Functor.map_comp] at h
        exact h }
  map_id F := by
    apply TranslationAction.Equivariant.Hom.ext
    exact (sheafRestrictScalars φ X).map_id F.obj
  map_comp α β := by
    apply TranslationAction.Equivariant.Hom.ext
    exact (sheafRestrictScalars φ X).map_comp α.hom β.hom

instance : (scalarRestrictionFunctor φ ρ).Faithful where
  map_injective h := by
    apply TranslationAction.Equivariant.Hom.ext
    apply (sheafRestrictScalars φ X).map_injective
    exact congrArg TranslationAction.Equivariant.Hom.hom h

/-- Forgetting geometric equivariance commutes with scalar restriction. -/
def scalarRestrictionForgetIso :
    scalarRestrictionFunctor φ ρ ⋙ TranslationAction.Equivariant.forget ≅
      TranslationAction.Equivariant.forget ⋙ sheafRestrictScalars φ X :=
  Iso.refl _

/-- Ordinary global sections commute with restriction of scalars. -/
def scalarRestrictionSectionsIso :
    sheafRestrictScalars φ X ⋙ EtaleDerivedSections.sections X R ≅
      EtaleDerivedSections.sections X S ⋙ ModuleCat.restrictScalars.{u} φ :=
  Functor.isoWhiskerLeft (sheafRestrictScalars φ X)
      (EtaleDerivedSections.sectionsIso X R) ≪≫
    Functor.isoWhiskerRight (EtaleDerivedSections.sectionsIso X S).symm
      (ModuleCat.restrictScalars.{u} φ)

variable {Y : Scheme.{u}} (τ : G →* (Aut Y)ᵐᵒᵖ)
variable (f : Y ⟶ X) [Etale f]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)

/-- Scalar restriction commutes with ordinary geometric restriction. -/
def scalarRestrictionPullbackIso :
    sheafRestrictScalars φ X ⋙ restriction f (ModuleCat.{u} R) ≅
      restriction f (ModuleCat.{u} S) ⋙ sheafRestrictScalars φ Y :=
  Iso.refl _

/-- Scalar restriction preserves the geometric translation/restriction comparison. -/
theorem scalarRestriction_equivariantRestrictionIso_inv
    (F : EtaleDerivedSections.ModuleSheaf X S) (g : G) :
    (equivariantRestrictionIso R ρ τ f hf g).inv.app
        ((sheafRestrictScalars φ X).obj F) =
      (sheafRestrictScalars φ Y).map
        ((equivariantRestrictionIso S ρ τ f hf g).inv.app F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp [equivariantRestrictionIso, restrictionComp, sheafRestrictScalars]
  simp only [Functor.map_comp, restrictionCongr_inv_component]
  rfl

/-- The two orders of coefficient-scalar restriction and geometric pullback
have the same equivariant structure maps. -/
theorem scalarRestriction_pullback_act (F : EquivariantSheaf S ρ) (g : G) :
    (equivariantPullbackObj R ρ τ f hf (scalarRestrictionObj φ ρ F)).act g =
      (scalarRestrictionObj φ τ (equivariantPullbackObj S ρ τ f hf F)).act g := by
  dsimp only [equivariantPullbackObj, scalarRestrictionObj]
  rw [Functor.map_comp, scalarRestriction_equivariantRestrictionIso_inv]
  rfl

/-- The identity on underlying sheaves compares the two orders of pullback
and restriction of scalars. -/
def scalarRestrictionPullbackObjIso (F : EquivariantSheaf S ρ) :
    equivariantPullbackObj R ρ τ f hf (scalarRestrictionObj φ ρ F) ≅
      scalarRestrictionObj φ τ (equivariantPullbackObj S ρ τ f hf F) :=
  TranslationAction.Equivariant.mkIso (Iso.refl _) (fun g => by
    change _ ≫ 𝟙 _ = (translateBy R τ g).map (𝟙 _) ≫ _
    erw [(translateBy R τ g).map_id, Category.comp_id, Category.id_comp]
    exact scalarRestriction_pullback_act φ ρ τ f hf F g)

set_option maxHeartbeats 800000 in
/-- Scalar restriction commutes naturally with equivariant geometric pullback. -/
def scalarRestrictionEquivariantPullbackIso :
    scalarRestrictionFunctor φ ρ ⋙ equivariantPullback R ρ τ f hf ≅
      equivariantPullback S ρ τ f hf ⋙ scalarRestrictionFunctor φ τ :=
  NatIso.ofComponents (scalarRestrictionPullbackObjIso φ ρ τ f hf)
    (fun {F E} α => by
      apply TranslationAction.Equivariant.Hom.ext
      change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [Category.comp_id, Category.id_comp]
      rfl)

/-- The global-section scalar comparison respects geometric restriction. -/
theorem scalarRestriction_sectionsMap (F : EtaleDerivedSections.ModuleSheaf X S) :
    (sectionsMap f R).app ((sheafRestrictScalars φ X).obj F) ≫
        (scalarRestrictionSectionsIso φ (X := Y)).hom.app
          ((restriction f (ModuleCat.{u} S)).obj F) =
      (scalarRestrictionSectionsIso φ (X := X)).hom.app F ≫
        (ModuleCat.restrictScalars.{u} φ).map ((sectionsMap f S).app F) := by
  dsimp [sectionsMap, scalarRestrictionSectionsIso]
  simp only [Functor.map_comp, Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(ModuleCat.restrictScalars.{u} φ).map_id, Category.id_comp]
  rfl

/-- The ordinary scalar comparison intertwines the geometric group actions. -/
theorem scalarRestriction_sectionsAction (F : EquivariantSheaf S ρ) (g : G) :
    ((pullbackSectionsFunctor R ρ).obj ((scalarRestrictionFunctor φ ρ).obj F)).ρ g ≫
        (scalarRestrictionSectionsIso φ (X := X)).hom.app F.obj =
      (scalarRestrictionSectionsIso φ (X := X)).hom.app F.obj ≫
        (ModuleCat.restrictScalars.{u} φ).map
          (((pullbackSectionsFunctor S ρ).obj F).ρ g) := by
  rw [pullbackSectionsFunctor_obj_ρ, pullbackSectionsFunctor_obj_ρ]
  dsimp only [scalarRestrictionFunctor, scalarRestrictionObj]
  have h := (scalarRestrictionSectionsIso φ (X := X)).hom.naturality (F.act g)
  dsimp only [Functor.comp_map] at h
  rw [Category.assoc]
  erw [h]
  rw [← Category.assoc]
  erw [scalarRestriction_sectionsMap φ (aut ρ g).hom F.obj]
  rw [Category.assoc, Functor.map_comp]

/-- Restricting scalars commutes naturally with the action on ordinary sections. -/
def scalarRestrictionSectionsFunctorIso :
    scalarRestrictionFunctor φ ρ ⋙ pullbackSectionsFunctor R ρ ≅
      pullbackSectionsFunctor S ρ ⋙ (ModuleCat.restrictScalars.{u} φ).mapAction G :=
  NatIso.ofComponents
    (fun F => Action.mkIso ((scalarRestrictionSectionsIso φ (X := X)).app F.obj)
      (scalarRestriction_sectionsAction φ ρ F))
    (fun {F E} α => by
      apply Action.Hom.ext
      simp only [Action.comp_hom, Functor.comp_map,
        pullbackSectionsFunctor_map_hom]
      change (EtaleDerivedSections.sections X R).map
          ((sheafRestrictScalars φ X).map α.hom) ≫
          (scalarRestrictionSectionsIso φ (X := X)).hom.app E.obj =
        (scalarRestrictionSectionsIso φ (X := X)).hom.app F.obj ≫
          (ModuleCat.restrictScalars.{u} φ).map
            (((pullbackSectionsFunctor S ρ).map α).hom)
      rw [pullbackSectionsFunctor_map_hom]
      exact (scalarRestrictionSectionsIso φ (X := X)).hom.naturality α.hom)

end Langlands.Geometry.EtaleCohomologyAction

