import Langlands.Geometry.EtaleActionFunctor
import Langlands.Geometry.EtaleCohomologyReindex

/-!
# Restriction of equivariant étale coefficients along group homomorphisms
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u w w' w''

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} (R : Type u) [CommRing R]
variable {G : Type w} [Group G] (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- Recover the equivariant sheaf from coefficients on the action diagram. -/
def toEquivariant (D : CoefficientDiagram R (actionSchemeDiagram ρ)) :
    EquivariantSheaf R ρ where
  obj := D.obj (SingleObj.star G)
  act g := D.map (i := SingleObj.star G) (j := SingleObj.star G) g
  act_one := by
    change D.map (i := SingleObj.star G) (j := SingleObj.star G) (1 : G) =
      (oneIso R ρ).hom.app (D.obj (SingleObj.star G))
    rw [← actionSchemeDiagram_restrictionId R ρ (SingleObj.star G)]
    exact D.map_id (SingleObj.star G)
  act_mul g h := by
    have hc := D.map_comp (i := SingleObj.star G) (j := SingleObj.star G)
      (k := SingleObj.star G) h g
    rw [actionSchemeDiagram_restrictionComp] at hc
    change D.map (i := SingleObj.star G) (j := SingleObj.star G) (g * h) =
      (compIso R ρ g h).inv.app (D.obj (SingleObj.star G)) ≫
        (translateBy R ρ g).map (D.map (i := SingleObj.star G) (j := SingleObj.star G) h) ≫
          D.map (i := SingleObj.star G) (j := SingleObj.star G) g
    exact ((compIso R ρ g h).app (D.obj (SingleObj.star G))).eq_inv_comp.mpr hc

/-- Reconstructing the equivariant sheaf is functorial in diagram coefficients. -/
def toEquivariantFunctor :
    CoefficientDiagram R (actionSchemeDiagram ρ) ⥤ EquivariantSheaf R ρ where
  obj := toEquivariant R ρ
  map f :=
    { hom := f.app (SingleObj.star G)
      comm g := f.comm (i := SingleObj.star G) (j := SingleObj.star G) g }

variable {H : Type w'} [Group H] (φ : H →* G)

/-- Precomposing the scheme-action diagram is the restricted scheme action. -/
theorem actionSchemeDiagram_comp :
    SingleObj.mapHom H G φ ⋙ actionSchemeDiagram ρ = actionSchemeDiagram (ρ.comp φ) := rfl

/-- Restriction of equivariant sheaves along a group homomorphism, obtained
by reindexing their compatible coefficients. -/
def restrictionFunctor : EquivariantSheaf R ρ ⥤ EquivariantSheaf R (ρ.comp φ) :=
  ofEquivariantFunctor R ρ ⋙
    CoefficientDiagram.reindexFunctor (SingleObj.mapHom H G φ) ⋙
    toEquivariantFunctor R (ρ.comp φ)

/-- Restriction retains the underlying sheaf. -/
@[simp] theorem restrictionFunctor_obj_obj (F : EquivariantSheaf R ρ) :
    ((restrictionFunctor R ρ φ).obj F).obj = F.obj := rfl

/-- Restriction evaluates the original structure map at the image element. -/
@[simp] theorem restrictionFunctor_obj_act (F : EquivariantSheaf R ρ) (h : H) :
    ((restrictionFunctor R ρ φ).obj F).act h = F.act (φ h) := rfl

/-- Restriction retains the underlying coefficient morphism. -/
@[simp] theorem restrictionFunctor_map_hom {F E : EquivariantSheaf R ρ} (f : F ⟶ E) :
    ((restrictionFunctor R ρ φ).map f).hom = f.hom := rfl

instance : (restrictionFunctor R ρ φ).Faithful where
  map_injective h := by
    apply TranslationAction.Equivariant.Hom.ext
    have hh := congrArg (fun f => f.hom) h
    exact hh

/-- The identity homomorphism restricts equivariant coefficients identically. -/
def restrictionIdIso : restrictionFunctor R ρ (MonoidHom.id G) ≅ 𝟭 (EquivariantSheaf R ρ) :=
  NatIso.ofComponents
    (fun F => TranslationAction.Equivariant.mkIso (Iso.refl F.obj) (fun g => by simp))
    (fun f => by apply TranslationAction.Equivariant.Hom.ext; simp)

/-- Successive restriction is restriction along the composite homomorphism. -/
def restrictionCompIso {K : Type w''} [Group K] (ψ : K →* H) :
    restrictionFunctor R ρ φ ⋙ restrictionFunctor R (ρ.comp φ) ψ ≅
      restrictionFunctor R ρ (φ.comp ψ) :=
  NatIso.ofComponents
    (fun F => TranslationAction.Equivariant.mkIso (Iso.refl F.obj) (fun g => by simp))
    (fun f => by apply TranslationAction.Equivariant.Hom.ext; simp)

/-- Every cohomology action restricts by evaluation at the homomorphism. -/
theorem restriction_cohomology_ρ (F : EquivariantSheaf R ρ) (q : ℕ) (h : H) :
    (pullbackCohomologyAction R (ρ.comp φ) ((restrictionFunctor R ρ φ).obj F) q).ρ h =
      (pullbackCohomologyAction R ρ F q).ρ (φ h) := by
  rw [pullbackCohomologyAction_ρ, pullbackCohomologyAction_ρ]
  rfl

/-- Restriction identifies the cohomology actions on the same ordinary module. -/
def restrictionCohomologyIso (F : EquivariantSheaf R ρ) (q : ℕ) :
    pullbackCohomologyAction R (ρ.comp φ) ((restrictionFunctor R ρ φ).obj F) q ≅
      (Action.res (ModuleCat.{u} R) φ).obj (pullbackCohomologyAction R ρ F q) :=
  Action.mkIso (Iso.refl ((EtaleDerivedSections.cohomology Y R q).obj F.obj))
    (fun h => by
      change (pullbackCohomologyAction R (ρ.comp φ) ((restrictionFunctor R ρ φ).obj F) q).ρ h ≫
        𝟙 _ = 𝟙 _ ≫ (pullbackCohomologyAction R ρ F q).ρ (φ h)
      rw [Category.comp_id, Category.id_comp]
      exact restriction_cohomology_ρ R ρ φ F q h)

/-- Taking ordinary cohomology commutes naturally with group restriction,
with identity maps on the underlying cohomology modules. -/
def restrictionCohomologyFunctorIso (q : ℕ) :
    restrictionFunctor R ρ φ ⋙ pullbackCohomologyFunctor R (ρ.comp φ) q ≅
      pullbackCohomologyFunctor R ρ q ⋙ Action.res (ModuleCat.{u} R) φ :=
  NatIso.ofComponents (fun F => restrictionCohomologyIso R ρ φ F q)
    (fun {F E} f => by
      apply Action.Hom.ext
      change (EtaleDerivedSections.cohomology Y R q).map f.hom ≫ 𝟙 _ =
        𝟙 _ ≫ (EtaleDerivedSections.cohomology Y R q).map f.hom
      rw [Category.comp_id, Category.id_comp])

/-- The cohomology restriction comparison is the identity on ordinary cohomology. -/
@[simp] theorem restrictionCohomologyFunctorIso_hom_app_hom
    (F : EquivariantSheaf R ρ) (q : ℕ) :
    ((restrictionCohomologyFunctorIso R ρ φ q).hom.app F).hom =
      𝟙 ((EtaleDerivedSections.cohomology Y R q).obj F.obj) := by
  change (restrictionCohomologyIso R ρ φ F q).hom.hom = _
  exact Action.mkIso_hom_hom _ _

/-- Global section actions likewise restrict by evaluation at the image element. -/
theorem restriction_sections_ρ (F : EquivariantSheaf R ρ) (h : H) :
    ((pullbackSectionsFunctor R (ρ.comp φ)).obj ((restrictionFunctor R ρ φ).obj F)).ρ h =
      ((pullbackSectionsFunctor R ρ).obj F).ρ (φ h) := rfl

/-- Restriction identifies the section actions on the same section module. -/
def restrictionSectionsIso (F : EquivariantSheaf R ρ) :
    (pullbackSectionsFunctor R (ρ.comp φ)).obj ((restrictionFunctor R ρ φ).obj F) ≅
      (Action.res (ModuleCat.{u} R) φ).obj ((pullbackSectionsFunctor R ρ).obj F) :=
  Action.mkIso (Iso.refl ((EtaleDerivedSections.sections Y R).obj F.obj))
    (fun h => by
      change ((pullbackSectionsFunctor R (ρ.comp φ)).obj
        ((restrictionFunctor R ρ φ).obj F)).ρ h ≫ 𝟙 _ =
        𝟙 _ ≫ ((pullbackSectionsFunctor R ρ).obj F).ρ (φ h)
      rw [Category.comp_id, Category.id_comp]
      exact restriction_sections_ρ R ρ φ F h)

/-- Global sections commute naturally with group restriction. -/
def restrictionSectionsFunctorIso :
    restrictionFunctor R ρ φ ⋙ pullbackSectionsFunctor R (ρ.comp φ) ≅
      pullbackSectionsFunctor R ρ ⋙ Action.res (ModuleCat.{u} R) φ :=
  NatIso.ofComponents (fun F => restrictionSectionsIso R ρ φ F)
    (fun {F E} f => by
      apply Action.Hom.ext
      change ((pullbackSectionsFunctor R (ρ.comp φ)).map
        ((restrictionFunctor R ρ φ).map f)).hom ≫ 𝟙 _ =
          𝟙 _ ≫ ((pullbackSectionsFunctor R ρ).map f).hom
      rw [Category.comp_id, Category.id_comp,
        pullbackSectionsFunctor_map_hom, pullbackSectionsFunctor_map_hom]
      rfl)

/-- The section restriction comparison is the identity on ordinary sections. -/
@[simp] theorem restrictionSectionsFunctorIso_hom_app_hom (F : EquivariantSheaf R ρ) :
    ((restrictionSectionsFunctorIso R ρ φ).hom.app F).hom = 𝟙 _ := rfl

/-- Restriction commutes with the canonical equivariant degree-zero comparison. -/
theorem restriction_cohomologyZero (F : EquivariantSheaf R ρ) :
    (restrictionCohomologyFunctorIso R ρ φ 0).hom.app F ≫
      (Action.res (ModuleCat.{u} R) φ).map ((pullbackCohomologyZeroFunctorIso R ρ).hom.app F) =
    (pullbackCohomologyZeroFunctorIso R (ρ.comp φ)).hom.app ((restrictionFunctor R ρ φ).obj F) ≫
      (restrictionSectionsFunctorIso R ρ φ).hom.app F := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, restrictionCohomologyFunctorIso_hom_app_hom,
    restrictionSectionsFunctorIso_hom_app_hom, Action.res_map_hom,
    pullbackCohomologyZeroFunctorIso_hom_app_hom]
  rfl

end Langlands.Geometry.EtaleCohomologyAction
