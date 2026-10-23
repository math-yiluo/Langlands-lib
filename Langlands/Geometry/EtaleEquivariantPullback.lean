import Langlands.Geometry.EtaleEquivariantMap

/-!
# Pullback of equivariant étale coefficient sheaves
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Cohomology EtalePullback

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (R : Type u) [CommRing R]

/-- Component of inverse restriction comparison along equal scheme morphisms. -/
theorem restrictionCongr_inv_component {f k : Y ⟶ X}
    [Etale f] [Etale k] (h : f = k)
    (F : EtaleDerivedSections.ModuleSheaf X R) (U : Y.Etaleᵒᵖ) :
    ((restrictionCongr R h).inv.app F).hom.app U =
      F.obj.map ((MorphismProperty.Over.mapCongr ⊤ h
        (inferInstance : Etale f)).hom.app U.unop).op := by
  subst k
  change 𝟙 _ = F.obj.map (𝟙 _)
  exact (F.obj.map_id _).symm

variable {G : Type w} [Group G]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (τ : G →* (Aut Y)ᵐᵒᵖ)
variable (f : Y ⟶ X) [Etale f]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)

/-- The inverse geometric restriction square respects the unit constraint. -/
theorem equivariantRestrictionIso_one (F : EtaleDerivedSections.ModuleSheaf X R) :
    (equivariantRestrictionIso R ρ τ f hf 1).inv.app F ≫
        (restriction f (ModuleCat.{u} R)).map ((oneIso R ρ).hom.app F) =
      (oneIso R τ).hom.app ((restriction f (ModuleCat.{u} R)).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp only [equivariantRestrictionIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]
  simp only [restrictionCongr_inv_component]
  dsimp [restrictionComp, oneIso, EtaleAutomorphism.translateCongr,
    EtaleAutomorphism.translateId]
  dsimp [restriction, translateBy, EtaleAutomorphism.translate, EtaleAutomorphism.sheafEquivalence]
  simp only [Category.comp_id, ← F.obj.map_comp]
  congr 1

/-- The inverse geometric restriction square respects multiplication. -/
theorem equivariantRestrictionIso_mul (F : EtaleDerivedSections.ModuleSheaf X R)
    (g h : G) :
    (equivariantRestrictionIso R ρ τ f hf (g * h)).inv.app F ≫
        (restriction f (ModuleCat.{u} R)).map ((compIso R ρ g h).inv.app F) =
      (compIso R τ g h).inv.app ((restriction f (ModuleCat.{u} R)).obj F) ≫
        (translateBy R τ g).map ((equivariantRestrictionIso R ρ τ f hf h).inv.app F) ≫
        (equivariantRestrictionIso R ρ τ f hf g).inv.app ((translateBy R ρ h).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp only [equivariantRestrictionIso, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom]
  simp only [restrictionCongr_inv_component]
  dsimp [restrictionComp, compIso, EtaleAutomorphism.translateCongr,
    EtaleAutomorphism.translateComp]
  dsimp [restriction, translateBy, EtaleAutomorphism.translate, EtaleAutomorphism.sheafEquivalence]
  simp only [restrictionCongr_inv_component, ← F.obj.map_comp]
  congr 1

/-- Restriction along an equivariant étale map, with its induced coefficient action. -/
def equivariantPullbackObj (F : EquivariantSheaf R ρ) : EquivariantSheaf R τ where
  obj := (restriction f (ModuleCat.{u} R)).obj F.obj
  act g := (equivariantRestrictionIso R ρ τ f hf g).inv.app F.obj ≫
    (restriction f (ModuleCat.{u} R)).map (F.act g)
  act_one := by
    rw [F.act_one]
    exact equivariantRestrictionIso_one R ρ τ f hf F.obj
  act_mul g h := by
    rw [F.act_mul]
    simp only [Functor.map_comp, ← Category.assoc]
    erw [equivariantRestrictionIso_mul R ρ τ f hf F.obj g h]
    have hn := (equivariantRestrictionIso R ρ τ f hf g).inv.naturality (F.act h)
    dsimp only [Functor.comp_map] at hn
    simp only [Category.assoc]
    rw [← Category.assoc ((equivariantRestrictionIso R ρ τ f hf g).inv.app _),
      ← hn]
    simp only [Category.assoc]
    rfl

/-- Equivariant pullback acts on coefficient morphisms by ordinary restriction. -/
def equivariantPullback : EquivariantSheaf R ρ ⥤ EquivariantSheaf R τ where
  obj := equivariantPullbackObj R ρ τ f hf
  map {F E} β :=
    { hom := (restriction f (ModuleCat.{u} R)).map β.hom
      comm g := by
        dsimp only [equivariantPullbackObj]
        rw [Category.assoc, ← Functor.map_comp, β.comm, Functor.map_comp,
          ← Category.assoc]
        exact congrArg (fun k => k ≫ (restriction f (ModuleCat.{u} R)).map (E.act g))
          ((equivariantRestrictionIso R ρ τ f hf g).inv.naturality β.hom).symm }
  map_id F := by
    apply TranslationAction.Equivariant.Hom.ext
    exact (restriction f (ModuleCat.{u} R)).map_id F.obj
  map_comp β γ := by
    apply TranslationAction.Equivariant.Hom.ext
    exact (restriction f (ModuleCat.{u} R)).map_comp β.hom γ.hom

/-- The underlying coefficient morphism of equivariant pullback is restriction. -/
@[simp] theorem equivariantPullback_map_hom {F E : EquivariantSheaf R ρ} (β : F ⟶ E) :
    ((equivariantPullback R ρ τ f hf).map β).hom =
      (restriction f (ModuleCat.{u} R)).map β.hom := rfl

/-- The identity coefficient map into the canonical equivariant pullback. -/
def equivariantPullbackCoefficient (F : EquivariantSheaf R ρ) :
    GeometricCoefficientMap R ρ τ f hf F ((equivariantPullback R ρ τ f hf).obj F) where
  hom := 𝟙 _
  comm g := by
    change (restriction f (ModuleCat.{u} R)).map (F.act g) ≫ 𝟙 _ =
      (equivariantRestrictionIso R ρ τ f hf g).hom.app F.obj ≫
        (translateBy R τ g).map (𝟙 _) ≫
          ((equivariantRestrictionIso R ρ τ f hf g).inv.app F.obj ≫
            (restriction f (ModuleCat.{u} R)).map (F.act g))
    erw [(translateBy R τ g).map_id]
    erw [Category.comp_id, Category.id_comp, Iso.hom_inv_id_app_assoc]

/-- Geometric restriction on ordinary equivariant cohomology is natural in coefficients. -/
def equivariantPullbackCohomology (q : ℕ) :
    pullbackCohomologyFunctor R ρ q ⟶
      equivariantPullback R ρ τ f hf ⋙ pullbackCohomologyFunctor R τ q where
  app F := (equivariantPullbackCoefficient R ρ τ f hf F).cohomologyMap q
  naturality {F E} β := by
    apply Action.Hom.ext
    change (EtaleDerivedSections.cohomology X R q).map β.hom ≫
        cohomologyMapWithCoefficients f R q (𝟙 _) =
      cohomologyMapWithCoefficients f R q (𝟙 _) ≫
        (EtaleDerivedSections.cohomology Y R q).map
          ((restriction f (ModuleCat.{u} R)).map β.hom)
    dsimp only [cohomologyMapWithCoefficients]
    erw [(EtaleDerivedSections.cohomology Y R q).map_id,
      (EtaleDerivedSections.cohomology Y R q).map_id]
    erw [Category.comp_id, Category.comp_id]
    exact (EtalePullback.cohomologyMap f R q).naturality β.hom

/-- Forgetting the action gives the ordinary derived geometric pullback. -/
@[simp] theorem equivariantPullbackCohomology_app_hom (q : ℕ) (F : EquivariantSheaf R ρ) :
    ((equivariantPullbackCohomology R ρ τ f hf q).app F).hom =
      (EtalePullback.cohomologyMap f R q).app F.obj := by
  change cohomologyMapWithCoefficients f R q (𝟙 _) = _
  dsimp only [cohomologyMapWithCoefficients]
  erw [(EtaleDerivedSections.cohomology Y R q).map_id]
  exact Category.comp_id _

/-- Geometric restriction on ordinary equivariant sections is natural in coefficients. -/
def equivariantPullbackSections :
    pullbackSectionsFunctor R ρ ⟶
      equivariantPullback R ρ τ f hf ⋙ pullbackSectionsFunctor R τ where
  app F := (equivariantPullbackCoefficient R ρ τ f hf F).sectionsMap
  naturality {F E} β := by
    apply Action.Hom.ext
    simp only [Action.comp_hom, Functor.comp_map, pullbackSectionsFunctor_map_hom,
      GeometricCoefficientMap.sectionsMap_hom, equivariantPullback_map_hom]
    change (EtaleDerivedSections.sections X R).map β.hom ≫
        ((EtalePullback.sectionsMap f R).app E.obj ≫
          (EtaleDerivedSections.sections Y R).map (𝟙 _)) =
      ((EtalePullback.sectionsMap f R).app F.obj ≫
        (EtaleDerivedSections.sections Y R).map (𝟙 _)) ≫
          (EtaleDerivedSections.sections Y R).map
            ((restriction f (ModuleCat.{u} R)).map β.hom)
    erw [(EtaleDerivedSections.sections Y R).map_id,
      (EtaleDerivedSections.sections Y R).map_id]
    erw [Category.comp_id, Category.comp_id]
    exact (EtalePullback.sectionsMap f R).naturality β.hom

/-- Forgetting the action gives ordinary restriction on sections. -/
@[simp] theorem equivariantPullbackSections_app_hom (F : EquivariantSheaf R ρ) :
    ((equivariantPullbackSections R ρ τ f hf).app F).hom =
      (EtalePullback.sectionsMap f R).app F.obj := by
  rw [equivariantPullbackSections, GeometricCoefficientMap.sectionsMap_hom]
  change (EtalePullback.sectionsMap f R).app F.obj ≫
    (EtaleDerivedSections.sections Y R).map (𝟙 _) = _
  erw [(EtaleDerivedSections.sections Y R).map_id]
  exact Category.comp_id _

/-- The canonical degree-zero comparison commutes with equivariant pullback. -/
theorem equivariantPullbackCohomology_zero (F : EquivariantSheaf R ρ) :
    (equivariantPullbackCohomology R ρ τ f hf 0).app F ≫
        (pullbackCohomologyZeroFunctorIso R τ).hom.app
          ((equivariantPullback R ρ τ f hf).obj F) =
      (pullbackCohomologyZeroFunctorIso R ρ).hom.app F ≫
        (equivariantPullbackSections R ρ τ f hf).app F :=
  (equivariantPullbackCoefficient R ρ τ f hf F).cohomologyMap_zero

end Langlands.Geometry.EtaleCohomologyAction
