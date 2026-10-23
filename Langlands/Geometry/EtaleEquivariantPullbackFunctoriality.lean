import Langlands.Geometry.EtaleEquivariantPullback

/-!
# Geometric functoriality of equivariant étale pullback
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Cohomology EtalePullback

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z : Scheme.{u}} (R : Type u) [CommRing R]
variable {G : Type w} [Group G]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (τ : G →* (Aut Y)ᵐᵒᵖ)
variable (υ : G →* (Aut Z)ᵐᵒᵖ)

/-- The identity scheme morphism is equivariant. -/
theorem equivariantMap_id (g : G) :
    (𝟙 X) ≫ (aut ρ g).hom = (aut ρ g).hom ≫ (𝟙 X) := by simp

/-- The geometric restriction square respects identity restriction. -/
theorem equivariantRestrictionIso_id (F : EtaleDerivedSections.ModuleSheaf X R)
    (g : G) :
    (equivariantRestrictionIso R ρ ρ (𝟙 X) (equivariantMap_id ρ) g).inv.app F ≫
        (restrictionId (ModuleCat.{u} R)).hom.app ((translateBy R ρ g).obj F) =
      (translateBy R ρ g).map ((restrictionId (ModuleCat.{u} R)).hom.app F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp only [equivariantRestrictionIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]
  simp only [restrictionCongr_inv_component]
  dsimp [restrictionComp, restrictionId, restriction, translateBy,
    EtaleAutomorphism.translate, EtaleAutomorphism.sheafEquivalence]
  simp only [Category.comp_id, ← F.obj.map_comp]
  congr 1

/-- Equivariant pullback along the identity is naturally the identity. -/
def equivariantPullbackId :
    equivariantPullback R ρ ρ (𝟙 X) (equivariantMap_id ρ) ≅
      𝟭 (EquivariantSheaf R ρ) :=
  NatIso.ofComponents
    (fun F => TranslationAction.Equivariant.mkIso
      ((restrictionId (ModuleCat.{u} R)).app F.obj) (fun g => by
        change ((equivariantRestrictionIso R ρ ρ (𝟙 X) (equivariantMap_id ρ) g).inv.app
          F.obj ≫ (restriction (𝟙 X) (ModuleCat.{u} R)).map (F.act g)) ≫
            (restrictionId (ModuleCat.{u} R)).hom.app F.obj = _
        rw [Category.assoc, (restrictionId (ModuleCat.{u} R)).hom.naturality,
          ← Category.assoc, equivariantRestrictionIso_id]
        rfl))
    (fun {F E} β => by
      apply TranslationAction.Equivariant.Hom.ext
      exact (restrictionId (ModuleCat.{u} R)).hom.naturality β.hom)

/-- The identity comparison retains the ordinary restriction comparison. -/
@[simp] theorem equivariantPullbackId_hom_app_hom (F : EquivariantSheaf R ρ) :
    ((equivariantPullbackId R ρ).hom.app F).hom =
      (restrictionId (ModuleCat.{u} R)).hom.app F.obj := rfl

/-- Identity geometric pullback acts as the identity on equivariant cohomology. -/
theorem equivariantPullbackCohomology_id (q : ℕ) (F : EquivariantSheaf R ρ) :
    (equivariantPullbackCohomology R ρ ρ (𝟙 X) (equivariantMap_id ρ) q).app F ≫
        (pullbackCohomologyFunctor R ρ q).map
          (X := (equivariantPullback R ρ ρ (𝟙 X) (equivariantMap_id ρ)).obj F) (Y := F)
          ((equivariantPullbackId R ρ).hom.app F) =
      𝟙 ((pullbackCohomologyFunctor R ρ q).obj F) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, equivariantPullbackCohomology_app_hom,
    pullbackCohomologyFunctor_map_hom, equivariantPullbackId_hom_app_hom, Action.id_hom]
  exact EtalePullback.cohomologyMap_id R q F.obj

/-- Identity geometric pullback acts as the identity on equivariant sections. -/
theorem equivariantPullbackSections_id (F : EquivariantSheaf R ρ) :
    (equivariantPullbackSections R ρ ρ (𝟙 X) (equivariantMap_id ρ)).app F ≫
        (pullbackSectionsFunctor R ρ).map
          (X := (equivariantPullback R ρ ρ (𝟙 X) (equivariantMap_id ρ)).obj F) (Y := F)
          ((equivariantPullbackId R ρ).hom.app F) =
      𝟙 ((pullbackSectionsFunctor R ρ).obj F) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, equivariantPullbackSections_app_hom,
    pullbackSectionsFunctor_map_hom, equivariantPullbackId_hom_app_hom, Action.id_hom]
  exact EtalePullback.sectionsMap_id R F.obj

variable (f : Y ⟶ X) [Etale f] (k : Z ⟶ Y) [Etale k]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)
variable (hk : ∀ g, k ≫ (aut τ g).hom = (aut υ g).hom ≫ k)

omit [Etale f] [Etale k] in
include hf hk in
/-- Composition of equivariant scheme morphisms is equivariant. -/
theorem equivariantMap_comp (g : G) :
    (k ≫ f) ≫ (aut ρ g).hom = (aut υ g).hom ≫ (k ≫ f) := by
  rw [Category.assoc, hf, ← Category.assoc k, hk, Category.assoc]

/-- The two geometric restriction squares respect composition restriction. -/
theorem equivariantRestrictionIso_comp
    (F : EtaleDerivedSections.ModuleSheaf X R) (g : G) :
    (equivariantRestrictionIso R τ υ k hk g).inv.app
        ((restriction f (ModuleCat.{u} R)).obj F) ≫
      (restriction k (ModuleCat.{u} R)).map
        ((equivariantRestrictionIso R ρ τ f hf g).inv.app F) ≫
      (restrictionComp f (ModuleCat.{u} R) k).hom.app ((translateBy R ρ g).obj F) =
    (translateBy R υ g).map ((restrictionComp f (ModuleCat.{u} R) k).hom.app F) ≫
      (equivariantRestrictionIso R ρ υ (k ≫ f)
        (equivariantMap_comp ρ τ υ f k hf hk) g).inv.app F := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp only [equivariantRestrictionIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]
  simp only [restrictionCongr_inv_component]
  dsimp [restrictionComp, restriction, translateBy,
    EtaleAutomorphism.translate, EtaleAutomorphism.sheafEquivalence]
  simp only [restrictionCongr_inv_component, ← F.obj.map_comp]
  congr 1

/-- Successive equivariant pullbacks identify naturally with composite pullback. -/
def equivariantPullbackComp :
    equivariantPullback R ρ τ f hf ⋙ equivariantPullback R τ υ k hk ≅
      equivariantPullback R ρ υ (k ≫ f) (equivariantMap_comp ρ τ υ f k hf hk) :=
  NatIso.ofComponents
    (fun F => TranslationAction.Equivariant.mkIso
      ((restrictionComp f (ModuleCat.{u} R) k).app F.obj) (fun g => by
        change ((equivariantRestrictionIso R τ υ k hk g).inv.app
          ((restriction f (ModuleCat.{u} R)).obj F.obj) ≫
          (restriction k (ModuleCat.{u} R)).map
            ((equivariantRestrictionIso R ρ τ f hf g).inv.app F.obj ≫
              (restriction f (ModuleCat.{u} R)).map (F.act g))) ≫
          (restrictionComp f (ModuleCat.{u} R) k).hom.app F.obj =
            (translateBy R υ g).map
              ((restrictionComp f (ModuleCat.{u} R) k).hom.app F.obj) ≫
            ((equivariantRestrictionIso R ρ υ (k ≫ f)
              (equivariantMap_comp ρ τ υ f k hf hk) g).inv.app F.obj ≫
                (restriction (k ≫ f) (ModuleCat.{u} R)).map (F.act g))
        rw [Functor.map_comp]
        simp only [Category.assoc]
        have hn := (restrictionComp f (ModuleCat.{u} R) k).hom.naturality (F.act g)
        dsimp only [Functor.comp_map] at hn
        erw [hn]
        have hc := equivariantRestrictionIso_comp R ρ τ υ f k hf hk F.obj g
        simpa only [Category.assoc] using congrArg
          (fun a => a ≫ (restriction (k ≫ f) (ModuleCat.{u} R)).map (F.act g)) hc))
    (fun {F E} β => by
      apply TranslationAction.Equivariant.Hom.ext
      exact (restrictionComp f (ModuleCat.{u} R) k).hom.naturality β.hom)

/-- The composition comparison retains the ordinary restriction comparison. -/
@[simp] theorem equivariantPullbackComp_hom_app_hom (F : EquivariantSheaf R ρ) :
    ((equivariantPullbackComp R ρ τ υ f k hf hk).hom.app F).hom =
      (restrictionComp f (ModuleCat.{u} R) k).hom.app F.obj := rfl

/-- Geometric cohomology maps compose through the equivariant comparison. -/
theorem equivariantPullbackCohomology_comp (q : ℕ) (F : EquivariantSheaf R ρ) :
    (equivariantPullbackCohomology R ρ τ f hf q).app F ≫
      (equivariantPullbackCohomology R τ υ k hk q).app
        ((equivariantPullback R ρ τ f hf).obj F) ≫
      (pullbackCohomologyFunctor R υ q).map
        ((equivariantPullbackComp R ρ τ υ f k hf hk).hom.app F) =
    (equivariantPullbackCohomology R ρ υ (k ≫ f)
      (equivariantMap_comp ρ τ υ f k hf hk) q).app F := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, equivariantPullbackCohomology_app_hom,
    pullbackCohomologyFunctor_map_hom, equivariantPullbackComp_hom_app_hom]
  exact EtalePullback.cohomologyMap_comp f R k q F.obj

/-- Geometric section maps compose through the equivariant comparison. -/
theorem equivariantPullbackSections_comp (F : EquivariantSheaf R ρ) :
    (equivariantPullbackSections R ρ τ f hf).app F ≫
      (equivariantPullbackSections R τ υ k hk).app
        ((equivariantPullback R ρ τ f hf).obj F) ≫
      (pullbackSectionsFunctor R υ).map
        ((equivariantPullbackComp R ρ τ υ f k hf hk).hom.app F) =
    (equivariantPullbackSections R ρ υ (k ≫ f)
      (equivariantMap_comp ρ τ υ f k hf hk)).app F := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, equivariantPullbackSections_app_hom,
    pullbackSectionsFunctor_map_hom, equivariantPullbackComp_hom_app_hom]
  exact EtalePullback.sectionsMap_comp f R k F.obj

end Langlands.Geometry.EtaleCohomologyAction
