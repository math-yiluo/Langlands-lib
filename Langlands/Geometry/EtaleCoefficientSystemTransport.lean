import Langlands.Geometry.EtaleCohomologyReindex
import Langlands.Geometry.EtaleEquivariantPullbackCoherence

/-! # Transport of systems of étale coefficients over a level diagram -/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory AlgebraicGeometry
open EtaleCohomologyAction (restrictionCongr_hom_component)

universe u v w v' w'

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option maxHeartbeats 800000

variable {R : Type u} [CommRing R]

private theorem restrictionComp_id_target {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    {e : X ⟶ X} [Etale e] (he : e = 𝟙 X) (F : EtaleDerivedSections.ModuleSheaf X R) :
    (restrictionComp e (ModuleCat.{u} R) f).hom.app F ≫
        (restrictionCongr R (show f ≫ e = f by rw [he, Category.comp_id])).hom.app F =
      (restriction f (ModuleCat.{u} R)).map
        ((restrictionCongr R he ≪≫ restrictionId (ModuleCat.{u} R)).hom.app F) := by
  subst e
  have hr : restrictionCongr R (rfl : 𝟙 X = 𝟙 X) = Iso.refl _ := rfl
  rw [hr, Iso.refl_trans]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [restrictionCongr_hom_component]
  dsimp [restrictionComp, restrictionId, restriction]
  simp only [Category.comp_id, ← F.obj.map_comp]
  congr 1

private theorem restrictionComp_id_source {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    {e : Y ⟶ Y} [Etale e] (he : e = 𝟙 Y) (F : EtaleDerivedSections.ModuleSheaf X R) :
    (restrictionComp f (ModuleCat.{u} R) e).hom.app F ≫
        (restrictionCongr R (show e ≫ f = f by rw [he, Category.id_comp])).hom.app F =
      (restrictionCongr R he ≪≫ restrictionId (ModuleCat.{u} R)).hom.app
        ((restriction f (ModuleCat.{u} R)).obj F) := by
  subst e
  have hr : restrictionCongr R (rfl : 𝟙 Y = 𝟙 Y) = Iso.refl _ := rfl
  rw [hr, Iso.refl_trans]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
  rw [restrictionCongr_hom_component]
  dsimp [restrictionComp, restrictionId, restriction]
  simp only [Category.comp_id, ← F.obj.map_comp]
  congr 1

variable {J : Type v} [Category.{w} J] {I : Type v'} [Category.{w'} I]
  {S : J ⥤ Scheme.{u}ᵒᵖ} [hS : ∀ {j j' : J} (a : j ⟶ j'), Etale (S.map a).unop]

namespace CoefficientDiagram

local notation "unitIso" j:max => (diagramRestrictionId R S j)
local notation "res" a:max => (diagramRestriction R S a)

variable (D : @CoefficientDiagram R _ (J × I) _ (CategoryTheory.Prod.fst J I ⋙ S)
  (fun {x y} (a : x ⟶ y) => hS a.1))

private def stageMap (j : J) {i i' : I} (c : i ⟶ i') :
    D.obj (j, i) ⟶ D.obj (j, i') :=
  (unitIso j).inv.app (D.obj (j, i)) ≫ D.map ((𝟙 j, c) : (j, i) ⟶ (j, i'))

private theorem unitIso_stageMap (j : J) {i i' : I} (c : i ⟶ i') :
    (unitIso j).hom.app (D.obj (j, i)) ≫ D.stageMap j c =
      D.map ((𝟙 j, c) : (j, i) ⟶ (j, i')) := by
  simp [stageMap]

private theorem stageMap_then_map {j j' : J} (a : j ⟶ j')
    {i i' i'' : I} (c : i ⟶ i') (d : i' ⟶ i'') :
    (res a).map (D.stageMap j c) ≫ D.map ((a, d) : (j, i') ⟶ (j', i'')) =
      D.map ((a, c ≫ d) : (j, i) ⟶ (j', i'')) := by
  let b : (j, i) ⟶ (j, i') := (𝟙 j, c)
  let g : (j, i') ⟶ (j', i'') := (a, d)
  let k : (j, i) ⟶ (j', i'') := (a, c ≫ d)
  have hcomp : k = b ≫ g := by
    apply Prod.hom_ext
    · exact (Category.id_comp a).symm
    · rfl
  have h := D.map_comp_transport b g k hcomp
  have he : (S.map (𝟙 j)).unop = 𝟙 (S.obj j).unop :=
    congrArg Quiver.Hom.unop (S.map_id j)
  have hu := restrictionComp_id_target (R := R) (S.map a).unop he (D.obj (j, i))
  simp only [Iso.trans_hom, NatTrans.comp_app] at h
  change ((restrictionComp (S.map (𝟙 j)).unop (ModuleCat.{u} R) (S.map a).unop).hom.app _ ≫
    (restrictionCongr R (show (S.map a).unop ≫ (S.map (𝟙 j)).unop = (S.map a).unop by
      rw [he, Category.comp_id])).hom.app _) ≫ D.map k = (res a).map (D.map b) ≫ D.map g at h
  rw [hu] at h
  change (res a).map ((unitIso j).hom.app (D.obj (j, i))) ≫ D.map k =
    (res a).map (D.map b) ≫ D.map g at h
  let ε := (unitIso j).inv.app (D.obj (j, i))
  have h' : (res a).map (ε ≫ (unitIso j).hom.app (D.obj (j, i))) ≫ D.map k =
      (res a).map (ε ≫ D.map b) ≫ D.map g := by
    simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
      congrArg (fun t => (res a).map ε ≫ t) h
  change (res a).map ((unitIso j).inv.app (D.obj (j, i)) ≫
    (unitIso j).hom.app (D.obj (j, i))) ≫ D.map k = _ at h'
  rw [Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp] at h'
  exact h'.symm

private theorem map_then_stageMap {j j' : J} (a : j ⟶ j')
    {i i' i'' : I} (c : i ⟶ i') (d : i' ⟶ i'') :
    D.map ((a, c) : (j, i) ⟶ (j', i')) ≫ D.stageMap j' (i' := i'') d =
      D.map ((a, c ≫ d) : (j, i) ⟶ (j', i'')) := by
  let b : (j, i) ⟶ (j', i') := (a, c)
  let g : (j', i') ⟶ (j', i'') := (𝟙 j', d)
  let k : (j, i) ⟶ (j', i'') := (a, c ≫ d)
  have hcomp : k = b ≫ g := by
    apply Prod.hom_ext
    · exact (Category.comp_id a).symm
    · rfl
  have h := D.map_comp_transport b g k hcomp
  have he : (S.map (𝟙 j')).unop = 𝟙 (S.obj j').unop :=
    congrArg Quiver.Hom.unop (S.map_id j')
  have hu := restrictionComp_id_source (R := R) (S.map a).unop he (D.obj (j, i))
  simp only [Iso.trans_hom, NatTrans.comp_app] at h
  change ((restrictionComp (S.map a).unop (ModuleCat.{u} R) (S.map (𝟙 j')).unop).hom.app _ ≫
    (restrictionCongr R (show (S.map (𝟙 j')).unop ≫ (S.map a).unop = (S.map a).unop by
      rw [he, Category.id_comp])).hom.app _) ≫ D.map k =
      (res (𝟙 j')).map (D.map b) ≫ D.map g at h
  rw [hu] at h
  change (unitIso j').hom.app ((res a).obj _) ≫ D.map k =
    (res (𝟙 j')).map (D.map b) ≫ D.map g at h
  rw [← unitIso_stageMap D j' d, (unitIso j').hom.naturality_assoc] at h
  change (unitIso j').hom.app ((res a).obj (D.obj (j, i))) ≫ D.map k =
    (unitIso j').hom.app ((res a).obj (D.obj (j, i))) ≫ D.map b ≫ D.stageMap j' d at h
  simpa only [Iso.inv_hom_id_app_assoc] using
    congrArg (fun t => (unitIso j').inv.app ((res a).obj (D.obj (j, i))) ≫ t) h.symm

/-- The coefficients at one level, with their stage maps after identifying identity
restriction with the identity functor. -/
def fiber (j : J) : I ⥤ EtaleDerivedSections.ModuleSheaf (S.obj j).unop R where
  obj i := D.obj (j, i)
  map c := D.stageMap j c
  map_id i := by
    change (unitIso j).inv.app (D.obj (j, i)) ≫ D.map (𝟙 (j, i)) = 𝟙 _
    rw [D.map_id]
    exact Iso.inv_hom_id_app (unitIso j) _
  map_comp {i i' i''} c d := by
    have h := D.map_then_stageMap (𝟙 j) c d
    rw [← unitIso_stageMap D j c, ← unitIso_stageMap D j (c ≫ d), Category.assoc] at h
    simpa only [Iso.inv_hom_id_app_assoc] using
      congrArg (fun t => (unitIso j).inv.app (D.obj (j, i)) ≫ t) h.symm

/-- The stage map recovers the original coefficient transition after identity restriction. -/
theorem fiber_map (j : J) {i i' : I} (c : i ⟶ i') :
    (unitIso j).hom.app (D.obj (j, i)) ≫ (fiber D j).map c =
      D.map ((𝟙 j, c) : (j, i) ⟶ (j, i')) :=
  D.unitIso_stageMap j c

/-- A level arrow induces a map of whole coefficient systems, after restriction
along its étale scheme morphism. -/
def fiberMap {j j' : J} (a : j ⟶ j') : fiber D j ⋙ res a ⟶ fiber D j' where
  app i := D.map ((a, 𝟙 i) : (j, i) ⟶ (j', i))
  naturality i i' c := by
    let transport (d : i ⟶ i') : (res a).obj (D.obj (j, i)) ⟶ D.obj (j', i') :=
      D.map ((a, d) : (j, i) ⟶ (j', i'))
    have hc := congrArg transport ((Category.comp_id c).trans (Category.id_comp c).symm)
    exact (D.stageMap_then_map a c (𝟙 i')).trans
      (hc.trans (D.map_then_stageMap a (𝟙 i) c).symm)

/-- The system map is the original coefficient transport at a fixed stage. -/
theorem fiberMap_app {j j' : J} (a : j ⟶ j') (i : I) :
    (fiberMap D a).app i = D.map ((a, 𝟙 i) : (j, i) ⟶ (j', i)) :=
  rfl

/-- Identity transport acts by the identity-restriction comparison. -/
theorem fiberMap_id (j : J) :
    fiberMap D (𝟙 j) = CategoryTheory.Functor.whiskerLeft (fiber D j) (unitIso j).hom := by
  apply NatTrans.ext
  funext i
  exact D.map_id (j, i)

/-- Successive level transports compose after the canonical restriction comparison. -/
theorem fiberMap_comp {j j' j'' : J} (a : j ⟶ j') (b : j' ⟶ j'') :
    CategoryTheory.Functor.whiskerLeft (fiber D j) (diagramRestrictionComp R S a b).hom ≫
        fiberMap D (a ≫ b) =
      CategoryTheory.Functor.whiskerRight (fiberMap D a) (res b) ≫ fiberMap D b := by
  apply NatTrans.ext
  funext i
  let a₁ : (j, i) ⟶ (j', i) := (a, 𝟙 i)
  let b₁ : (j', i) ⟶ (j'', i) := (b, 𝟙 i)
  let c : (j, i) ⟶ (j'', i) := (a ≫ b, 𝟙 i)
  have hc : c = a₁ ≫ b₁ := by
    apply Prod.hom_ext
    · rfl
    · exact (Category.id_comp (𝟙 i)).symm
  exact D.map_comp_transport a₁ b₁ c hc

end CoefficientDiagram

end Langlands.Geometry.EtalePullback
