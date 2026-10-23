import Langlands.Geometry.EtaleEquivariantCoefficientDiagram
import Langlands.Geometry.EtaleCohomologyFixedDiagram

/-!
# Fixed-scheme equivariant coefficient diagrams
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u v w t

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme.{u}} (R : Type u) [CommRing R]
variable {G : Type t} [Group G] (ρ : G →* (Aut X)ᵐᵒᵖ)
variable (J : Type v) [Category.{w} J]

namespace EquivariantCoefficientDiagram

/-- An equivariant sheaf diagram on one scheme gives compatible equivariant
coefficients on the constant opposite-scheme diagram. -/
def ofFixed (D : J ⥤ EquivariantSheaf R ρ) :
    EquivariantCoefficientDiagram R (fixedSchemeDiagram X J) (fun _ => ρ)
      (fun _ => equivariantMap_id ρ) where
  obj i := D.obj i
  map a := (equivariantPullbackId R ρ).hom.app (D.obj _) ≫ D.map a
  map_id i := by
    apply TranslationAction.Equivariant.Hom.ext
    simpa only [TranslationAction.Equivariant.comp_hom,
      equivariantPullbackId_hom_app_hom, equivariantDiagramRestrictionId_hom_app_hom,
      CoefficientDiagram.ofFixed, Functor.comp_obj, Functor.comp_map,
      TranslationAction.Equivariant.forget] using
      (CoefficientDiagram.ofFixed X R J
        (D ⋙ TranslationAction.Equivariant.forget)).map_id i
  map_comp a b := by
    apply TranslationAction.Equivariant.Hom.ext
    simpa only [TranslationAction.Equivariant.comp_hom,
      equivariantPullbackId_hom_app_hom, equivariantDiagramRestrictionComp_hom_app_hom,
      equivariantPullback_map_hom, CoefficientDiagram.ofFixed, Functor.comp_obj,
      Functor.comp_map, TranslationAction.Equivariant.forget] using
      (CoefficientDiagram.ofFixed X R J
        (D ⋙ TranslationAction.Equivariant.forget)).map_comp a b

/-- Forgetting the fixed-scheme equivariant construction recovers its ordinary counterpart. -/
theorem ofFixed_forget (D : J ⥤ EquivariantSheaf R ρ) :
    (ofFixed R ρ J D).forget =
      CoefficientDiagram.ofFixed X R J (D ⋙ TranslationAction.Equivariant.forget) := rfl

/-- A natural transformation of equivariant sheaf diagrams gives compatible coefficients. -/
def ofFixedMap {D E : J ⥤ EquivariantSheaf R ρ} (α : D ⟶ E) :
    ofFixed R ρ J D ⟶ ofFixed R ρ J E where
  app i := α.app i
  comm a := by
    apply TranslationAction.Equivariant.Hom.ext
    simpa only [ofFixed, TranslationAction.Equivariant.comp_hom,
      equivariantPullbackId_hom_app_hom, equivariantPullback_map_hom,
      CoefficientDiagram.ofFixed, CoefficientDiagram.ofFixedMap,
      Functor.comp_obj, Functor.comp_map, Functor.whiskerRight_app,
      TranslationAction.Equivariant.forget] using
      (CoefficientDiagram.ofFixedMap X R J
        (Functor.whiskerRight α TranslationAction.Equivariant.forget)).comm a

/-- Fixed-scheme equivariant coefficient diagrams depend functorially on their sheaves. -/
def ofFixedFunctor : (J ⥤ EquivariantSheaf R ρ) ⥤
    EquivariantCoefficientDiagram R (fixedSchemeDiagram X J) (fun _ => ρ)
      (fun _ => equivariantMap_id ρ) where
  obj := ofFixed R ρ J
  map := ofFixedMap R ρ J
  map_id D := by apply Hom.ext; rfl
  map_comp α β := by apply Hom.ext; rfl

instance : (ofFixedFunctor R ρ J).Faithful where
  map_injective h := by
    apply NatTrans.ext
    funext i
    exact congrArg (fun α => α.app i) h

/-- Ordinary forgetting commutes naturally with the fixed-scheme construction. -/
def ofFixedForgetFunctorIso :
    ofFixedFunctor R ρ J ⋙ forgetFunctor ≅
      (Functor.whiskeringRight J (EquivariantSheaf R ρ)
        (EtaleDerivedSections.ModuleSheaf X R)).obj
          TranslationAction.Equivariant.forget ⋙
        CoefficientDiagram.ofFixedFunctor X R J :=
  Iso.refl _

/-- Evaluation of fixed-scheme coefficients retains the original equivariant sheaf. -/
def ofFixedEvaluationIso (i : J) :
    ofFixedFunctor R ρ J ⋙ evaluation i ≅
      (CategoryTheory.evaluation J (EquivariantSheaf R ρ)).obj i :=
  Iso.refl _

/-- The cohomology transition is the original equivariant coefficient map on cohomology. -/
theorem ofFixed_cohomology_map (D : J ⥤ EquivariantSheaf R ρ) (q : ℕ)
    {i j : J} (a : i ⟶ j) :
    ((ofFixed R ρ J D).cohomology q).map a =
      (pullbackCohomologyFunctor R ρ q).map (D.map a) := by
  apply Action.Hom.ext
  rw [cohomology_map_hom, pullbackCohomologyFunctor_map_hom]
  exact CoefficientDiagram.ofFixed_cohomology_map X R J
    (D ⋙ TranslationAction.Equivariant.forget) q a

set_option maxHeartbeats 600000 in
/-- The section transition is the original equivariant coefficient map on sections. -/
theorem ofFixed_sections_map (D : J ⥤ EquivariantSheaf R ρ)
    {i j : J} (a : i ⟶ j) :
    (ofFixed R ρ J D).sections.map a =
      (pullbackSectionsFunctor R ρ).map (D.map a) := by
  apply Action.Hom.ext
  rw [sections_map_hom, pullbackSectionsFunctor_map_hom, CoefficientDiagram.sections_map]
  change (EtalePullback.sectionsMap (𝟙 X) R).app (D.obj i).obj ≫
      (EtaleDerivedSections.sections X R).map
        ((restrictionId (ModuleCat.{u} R)).hom.app (D.obj i).obj ≫ (D.map a).hom) = _
  rw [Functor.map_comp, ← Category.assoc, EtalePullback.sectionsMap_id, Category.id_comp]

/-- The varying-scheme construction specializes to postcomposition by equivariant cohomology. -/
def ofFixedCohomologyIso (D : J ⥤ EquivariantSheaf R ρ) (q : ℕ) :
    (ofFixed R ρ J D).cohomology q ≅ D ⋙ pullbackCohomologyFunctor R ρ q :=
  NatIso.ofComponents (fun i => Iso.refl _) (fun {i j} a => by
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp, Functor.comp_map]
      using ofFixed_cohomology_map R ρ J D q a)

/-- The analogous specialization for ordinary sections retains their geometric action. -/
def ofFixedSectionsIso (D : J ⥤ EquivariantSheaf R ρ) :
    (ofFixed R ρ J D).sections ≅ D ⋙ pullbackSectionsFunctor R ρ :=
  NatIso.ofComponents (fun i => Iso.refl _) (fun {i j} a => by
    simpa only [Iso.refl_hom, Category.comp_id, Category.id_comp, Functor.comp_map]
      using ofFixed_sections_map R ρ J D a)

/-- The cohomology specialization is natural in the full coefficient diagram. -/
def ofFixedCohomologyFunctorIso (q : ℕ) :
    ofFixedFunctor R ρ J ⋙ cohomologyFunctor q ≅
      (Functor.whiskeringRight J (EquivariantSheaf R ρ)
        (Action (ModuleCat.{u} R) G)).obj (pullbackCohomologyFunctor R ρ q) :=
  NatIso.ofComponents (fun D => ofFixedCohomologyIso R ρ J D q) (fun {D E} α => by
    apply NatTrans.ext
    funext i
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The section specialization is natural in the full coefficient diagram. -/
def ofFixedSectionsFunctorIso :
    ofFixedFunctor R ρ J ⋙ sectionsFunctor ≅
      (Functor.whiskeringRight J (EquivariantSheaf R ρ)
        (Action (ModuleCat.{u} R) G)).obj (pullbackSectionsFunctor R ρ) :=
  NatIso.ofComponents (fun D => ofFixedSectionsIso R ρ J D) (fun {D E} α => by
    apply NatTrans.ext
    funext i
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- The canonical degree-zero comparison remains the original vertexwise comparison. -/
theorem ofFixed_cohomologyZeroIso_hom_app (D : J ⥤ EquivariantSheaf R ρ) (i : J) :
    (cohomologyZeroIso (ofFixed R ρ J D)).hom.app i =
      (pullbackCohomologyZeroFunctorIso R ρ).hom.app (D.obj i) := rfl

/-- The inverse degree-zero comparison also remains the original vertexwise comparison. -/
theorem ofFixed_cohomologyZeroIso_inv_app (D : J ⥤ EquivariantSheaf R ρ) (i : J) :
    (cohomologyZeroIso (ofFixed R ρ J D)).inv.app i =
      (pullbackCohomologyZeroFunctorIso R ρ).inv.app (D.obj i) := rfl

end EquivariantCoefficientDiagram

end Langlands.Geometry.EtaleCohomologyAction
