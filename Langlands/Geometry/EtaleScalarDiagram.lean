import Langlands.Geometry.EtaleScalarRestriction
import Langlands.Geometry.EtaleEquivariantCoefficientDiagram

/-!
# Scalar restriction of compatible equivariant coefficients
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
variable {J : Type v} [Category.{w} J] {S : J ⥤ Scheme.{u}ᵒᵖ}
variable [∀ {i j : J} (a : i ⟶ j), Etale (S.map a).unop]

/-- Scalar restriction preserves the identity comparison of geometric restriction. -/
theorem scalarRestriction_diagramRestrictionId (i : J)
    (F : EtaleDerivedSections.ModuleSheaf (S.obj i).unop A) :
    (sheafRestrictScalars φ (S.obj i).unop).map
        ((diagramRestrictionId A S i).hom.app F) =
      (diagramRestrictionId R S i).hom.app
        ((sheafRestrictScalars φ (S.obj i).unop).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp [diagramRestrictionId, sheafRestrictScalars, restrictionId]
  simp only [Functor.map_comp, restrictionCongr_hom_component,
    Category.comp_id]
  rfl

/-- Scalar restriction preserves the composition comparison of geometric restriction. -/
theorem scalarRestriction_diagramRestrictionComp
    {i j k : J} (a : i ⟶ j) (b : j ⟶ k)
    (F : EtaleDerivedSections.ModuleSheaf (S.obj i).unop A) :
    (sheafRestrictScalars φ (S.obj k).unop).map
        ((diagramRestrictionComp A S a b).hom.app F) =
      (diagramRestrictionComp R S a b).hom.app
        ((sheafRestrictScalars φ (S.obj i).unop).obj F) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  dsimp [diagramRestrictionComp, sheafRestrictScalars, restrictionComp]
  simp only [Functor.map_comp, restrictionCongr_hom_component]
  rfl

variable {G : Type t} [Group G] {ρ : ∀ i, G →* (Aut (S.obj i).unop)ᵐᵒᵖ}
variable {hρ : ∀ {i j : J} (a : i ⟶ j) (g : G),
  (S.map a).unop ≫ (aut (ρ i) g).hom = (aut (ρ j) g).hom ≫ (S.map a).unop}

namespace EquivariantCoefficientDiagram

set_option maxHeartbeats 800000 in
/-- Restrict each coefficient ring action and each compatible transition map. -/
def restrictScalars (D : EquivariantCoefficientDiagram A S ρ hρ) :
    EquivariantCoefficientDiagram R S ρ hρ where
  obj i := (scalarRestrictionFunctor φ (ρ i)).obj (D.obj i)
  map {i j} a :=
    (scalarRestrictionPullbackObjIso φ (ρ i) (ρ j) (S.map a).unop (hρ a)
        (D.obj i)).hom ≫
      (scalarRestrictionFunctor φ (ρ j)).map (D.map a)
  map_id i := by
    apply TranslationAction.Equivariant.Hom.ext
    rw [equivariantDiagramRestrictionId_hom_app_hom]
    change 𝟙 _ ≫ (sheafRestrictScalars φ (S.obj i).unop).map (D.map (𝟙 i)).hom = _
    rw [Category.id_comp]
    change (sheafRestrictScalars φ (S.obj i).unop).map (D.forget.map (𝟙 i)) = _
    rw [D.forget.map_id, scalarRestriction_diagramRestrictionId]
    rfl
  map_comp {i j k} a b := by
    apply TranslationAction.Equivariant.Hom.ext
    simp only [TranslationAction.Equivariant.comp_hom,
      equivariantDiagramRestrictionComp_hom_app_hom, equivariantPullback_map_hom]
    change _ ≫ (𝟙 _ ≫ (sheafRestrictScalars φ (S.obj k).unop).map (D.map (a ≫ b)).hom) =
      (restriction (S.map b).unop (ModuleCat.{u} R)).map
        (𝟙 _ ≫ (sheafRestrictScalars φ (S.obj j).unop).map (D.map a).hom) ≫
      (𝟙 _ ≫ (sheafRestrictScalars φ (S.obj k).unop).map (D.map b).hom)
    simp only [Category.id_comp]
    erw [← scalarRestriction_diagramRestrictionComp φ a b (D.obj i).obj]
    rw [← Functor.map_comp]
    have h := congrArg (fun f => (sheafRestrictScalars φ (S.obj k).unop).map f)
      (D.forget.map_comp a b)
    simp only [Functor.map_comp, forget] at h
    exact h

/-- Scalar restriction retains a transition's underlying additive map. -/
@[simp] theorem restrictScalars_map_hom
    (D : EquivariantCoefficientDiagram A S ρ hρ) {i j : J} (a : i ⟶ j) :
    ((restrictScalars φ D).map a).hom =
      (sheafRestrictScalars φ (S.obj j).unop).map (D.map a).hom := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

/-- Restrict each component of a compatible coefficient morphism. -/
def restrictScalarsMap {D E : EquivariantCoefficientDiagram A S ρ hρ} (α : D ⟶ E) :
    restrictScalars φ D ⟶ restrictScalars φ E where
  app i := (scalarRestrictionFunctor φ (ρ i)).map (α.app i)
  comm {i j} a := by
    apply TranslationAction.Equivariant.Hom.ext
    simp only [TranslationAction.Equivariant.comp_hom, restrictScalars_map_hom,
      equivariantPullback_map_hom]
    have h := congrArg (fun f => (sheafRestrictScalars φ (S.obj j).unop).map f)
      (congrArg TranslationAction.Equivariant.Hom.hom (α.comm a))
    simp only [TranslationAction.Equivariant.comp_hom, equivariantPullback_map_hom,
      Functor.map_comp] at h
    exact h

/-- Restriction of coefficient scalars on the category of compatible diagrams. -/
def restrictScalarsFunctor :
    EquivariantCoefficientDiagram A S ρ hρ ⥤ EquivariantCoefficientDiagram R S ρ hρ where
  obj := restrictScalars φ
  map := restrictScalarsMap φ
  map_id D := by
    apply Hom.ext
    funext i
    exact (scalarRestrictionFunctor φ (ρ i)).map_id (D.obj i)
  map_comp α β := by
    apply Hom.ext
    funext i
    exact (scalarRestrictionFunctor φ (ρ i)).map_comp (α.app i) (β.app i)

instance : (restrictScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) φ).Faithful where
  map_injective h := by
    apply Hom.ext
    funext i
    apply (scalarRestrictionFunctor φ (ρ i)).map_injective
    exact congrArg (fun α => α.app i) h

/-- Evaluation commutes with coefficient scalar restriction. -/
def restrictScalarsEvaluationIso (i : J) :
    restrictScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) φ ⋙ evaluation i ≅
      evaluation i ⋙ scalarRestrictionFunctor φ (ρ i) :=
  Iso.refl _

/-- The ordinary section diagrams compare by the canonical vertexwise isomorphisms. -/
def restrictScalarsSectionsIso (D : EquivariantCoefficientDiagram A S ρ hρ) :
    (restrictScalars φ D).sections ≅
      D.sections ⋙ (ModuleCat.restrictScalars.{u} φ).mapAction G :=
  NatIso.ofComponents
    (fun i => (scalarRestrictionSectionsFunctorIso φ (ρ i)).app (D.obj i))
    (fun {i j} a => by
      apply Action.Hom.ext
      simp only [Action.comp_hom, sections_map_hom, CoefficientDiagram.sections_map]
      change _ ≫ (scalarRestrictionSectionsIso φ (X := (S.obj j).unop)).hom.app
          (D.obj j).obj =
        (scalarRestrictionSectionsIso φ (X := (S.obj i).unop)).hom.app (D.obj i).obj ≫ _
      simp only [forget, restrictScalars_map_hom]
      rw [Category.assoc]
      erw [(scalarRestrictionSectionsIso φ (X := (S.obj j).unop)).hom.naturality
        (D.map a).hom]
      rw [← Category.assoc]
      erw [scalarRestriction_sectionsMap φ (S.map a).unop (D.obj i).obj]
      simp only [Category.assoc, Functor.comp_map, Functor.mapAction_map_hom,
        sections_map_hom, CoefficientDiagram.sections_map, Functor.map_comp]
      rfl)

/-- The section comparison is natural in compatible equivariant coefficient diagrams. -/
def restrictScalarsSectionsFunctorIso :
    restrictScalarsFunctor (S := S) (ρ := ρ) (hρ := hρ) φ ⋙ sectionsFunctor ≅
      sectionsFunctor ⋙
        (Functor.whiskeringRight J (Action (ModuleCat.{u} A) G)
          (Action (ModuleCat.{u} R) G)).obj
            ((ModuleCat.restrictScalars.{u} φ).mapAction G) :=
  NatIso.ofComponents (restrictScalarsSectionsIso φ)
    (fun {D E} α => by
      apply NatTrans.ext
      funext i
      exact (scalarRestrictionSectionsFunctorIso φ (ρ i)).hom.naturality (α.app i))

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
