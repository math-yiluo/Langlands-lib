import Langlands.Geometry.EtaleAutomorphismPullback
import Langlands.Geometry.EtaleCohomologyDiagram

/-!
# Equivariant coefficients as a varying-scheme diagram
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry Opposite
open Langlands.Cohomology EtalePullback

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} (R : Type u) [CommRing R]
variable {G : Type w} [Group G] (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- The opposite-scheme diagram encoded by a group action. -/
def actionSchemeDiagram : SingleObj G ⥤ Scheme.{u}ᵒᵖ where
  obj _ := op Y
  map g := (aut ρ g).hom.op
  map_id _ := by
    change (aut ρ 1).hom.op = (𝟙 Y).op
    rw [aut_one]
    rfl
  map_comp g h := by
    change (aut ρ (h * g)).hom.op = ((aut ρ g).hom.op ≫ (aut ρ h).hom.op)
    rw [aut_mul]
    rfl

instance {i j : SingleObj G} (g : i ⟶ j) :
    Etale ((actionSchemeDiagram ρ).map g).unop :=
  inferInstanceAs (Etale (aut ρ g).hom)

/-- Equality transport for restriction agrees with translation transport. -/
theorem restrictionCongr_translateCongr {σ τ : Y ≅ Y} (h : σ = τ) :
    restrictionCongr R (congrArg Iso.hom h) =
      EtaleAutomorphism.translateCongr (ModuleCat.{u} R) h := by
  subst τ
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change 𝟙 _ = F.obj.map (𝟙 _)
  exact (F.obj.map_id _).symm

/-- The diagram unit constraint is the translation unit constraint. -/
theorem actionSchemeDiagram_restrictionId (i : SingleObj G) :
    diagramRestrictionId R (actionSchemeDiagram ρ) i = oneIso R ρ := by
  change restrictionCongr R _ ≪≫ restrictionId (ModuleCat.{u} R) = _
  rw [restrictionCongr_translateCongr R (aut_one ρ)]
  rfl

/-- The diagram composition constraint is the translation composition constraint. -/
theorem actionSchemeDiagram_restrictionComp {i j k : SingleObj G}
    (g : i ⟶ j) (h : j ⟶ k) :
    diagramRestrictionComp R (actionSchemeDiagram ρ) g h = compIso R ρ h g := by
  change restrictionComp (aut ρ g).hom (ModuleCat.{u} R) (aut ρ h).hom ≪≫
    restrictionCongr R _ = _
  rw [restrictionCongr_translateCongr R (aut_mul ρ h g).symm]
  rfl

/-- An actual equivariant sheaf gives compatible coefficients on the group
action's opposite-scheme diagram. -/
def ofEquivariant (F : EquivariantSheaf R ρ) :
    CoefficientDiagram R (actionSchemeDiagram ρ) where
  obj _ := F.obj
  map g := F.act g
  map_id i := by
    rw [actionSchemeDiagram_restrictionId]
    exact F.act_one
  map_comp g h := by
    rw [actionSchemeDiagram_restrictionComp]
    change (compIso R ρ h g).hom.app F.obj ≫ F.act (h * g) = _
    rw [F.act_mul]
    simp only [data, Iso.hom_inv_id_app_assoc]
    rfl

/-- Cohomology of the compatible coefficients has exactly the geometric
pullback action as its arrow maps. -/
theorem ofEquivariant_cohomology_map (F : EquivariantSheaf R ρ) (q : ℕ)
    {i j : SingleObj G} (g : i ⟶ j) :
    ((ofEquivariant R ρ F).cohomology q).map g =
      (pullbackCohomologyAction R ρ F q).ρ g :=
  (pullbackCohomologyAction_ρ R ρ F q g).symm

/-- The compatible-coefficient cohomology diagram is the diagram associated
to the geometric pullback action, with identity comparison components. -/
def ofEquivariantCohomologyIso (F : EquivariantSheaf R ρ) (q : ℕ) :
    (ofEquivariant R ρ F).cohomology q ≅
      (Action.functorCategoryEquivalence (ModuleCat.{u} R) G).functor.obj
        (pullbackCohomologyAction R ρ F q) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun g => by
    change ((ofEquivariant R ρ F).cohomology q).map g ≫ 𝟙 _ =
      𝟙 _ ≫ (pullbackCohomologyAction R ρ F q).ρ g
    rw [Category.comp_id, Category.id_comp]
    exact ofEquivariant_cohomology_map R ρ F q g)

/-- The existing translation cohomology action, viewed as a group diagram,
agrees with cohomology of the constructed compatible coefficients. -/
def translationCohomologyDiagramIso (F : EquivariantSheaf R ρ) (q : ℕ) :
    (Action.functorCategoryEquivalence (ModuleCat.{u} R) G).functor.obj
        (TranslationAction.cohomologyAction (sectionsTop R) F
          (injectiveResolution F.obj) q) ≅
      (ofEquivariant R ρ F).cohomology q :=
  (Action.functorCategoryEquivalence (ModuleCat.{u} R) G).functor.mapIso
      (pullbackCohomologyActionIso R ρ F q) ≪≫
    (ofEquivariantCohomologyIso R ρ F q).symm

end Langlands.Geometry.EtaleCohomologyAction
