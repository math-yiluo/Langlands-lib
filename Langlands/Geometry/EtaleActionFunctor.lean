import Langlands.Cohomology.TranslationEquivariantCategory
import Langlands.Geometry.EtaleActionDiagram
import Langlands.Geometry.EtaleCohomologyDiagramFunctor

/-!
# Cohomology functors on equivariant étale coefficients
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} (R : Type u) [CommRing R]
variable {G : Type w} [Group G] (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- Converting equivariant sheaves to compatible coefficients is functorial. -/
def ofEquivariantFunctor :
    EquivariantSheaf R ρ ⥤ CoefficientDiagram R (actionSchemeDiagram ρ) where
  obj := ofEquivariant R ρ
  map f :=
    { app := fun _ => f.hom
      comm := fun g => f.comm g }

instance : (ofEquivariantFunctor R ρ).Faithful where
  map_injective h := by
    apply TranslationAction.Equivariant.Hom.ext
    exact congrArg (fun f => f.app (SingleObj.star G)) h

/-- A coefficient morphism induces an equivariant map on ordinary cohomology. -/
def pullbackCohomologyMap {F E : EquivariantSheaf R ρ} (f : F ⟶ E) (q : ℕ) :
    pullbackCohomologyAction R ρ F q ⟶ pullbackCohomologyAction R ρ E q where
  hom := (EtaleDerivedSections.cohomology Y R q).map f.hom
  comm g := by
    rw [← ofEquivariant_cohomology_map R ρ F q
        (i := SingleObj.star G) (j := SingleObj.star G) g,
      ← ofEquivariant_cohomology_map R ρ E q
        (i := SingleObj.star G) (j := SingleObj.star G) g]
    exact (CoefficientDiagram.cohomologyMap
      ((ofEquivariantFunctor R ρ).map f) q).naturality
        (X := SingleObj.star G) (Y := SingleObj.star G) g

/-- Ordinary cohomology in every degree, with its geometric group action,
is a functor of equivariant coefficient sheaves. -/
def pullbackCohomologyFunctor (q : ℕ) :
    EquivariantSheaf R ρ ⥤ Action (ModuleCat.{u} R) G where
  obj F := pullbackCohomologyAction R ρ F q
  map f := pullbackCohomologyMap R ρ f q
  map_id F := by
    apply Action.Hom.ext
    exact (EtaleDerivedSections.cohomology Y R q).map_id F.obj
  map_comp f h := by
    apply Action.Hom.ext
    exact (EtaleDerivedSections.cohomology Y R q).map_comp f.hom h.hom

/-- The underlying map is precisely the usual right-derived map of the
coefficient-sheaf morphism. -/
@[simp] theorem pullbackCohomologyFunctor_map_hom {F E : EquivariantSheaf R ρ}
    (f : F ⟶ E) (q : ℕ) :
    ((pullbackCohomologyFunctor R ρ q).map f).hom =
      (EtaleDerivedSections.cohomology Y R q).map f.hom := rfl

/-- The action-diagram comparison is natural also in the equivariant
coefficient sheaf. -/
def ofEquivariantCohomologyFunctorIso (q : ℕ) :
    ofEquivariantFunctor R ρ ⋙ CoefficientDiagram.cohomologyFunctor q ≅
      pullbackCohomologyFunctor R ρ q ⋙
        (Action.functorCategoryEquivalence (ModuleCat.{u} R) G).functor :=
  NatIso.ofComponents (fun F => ofEquivariantCohomologyIso R ρ F q)
    (fun {F E} f => by
      apply NatTrans.ext
      funext i
      change (EtaleDerivedSections.cohomology Y R q).map f.hom ≫ 𝟙 _ =
        𝟙 _ ≫ (EtaleDerivedSections.cohomology Y R q).map f.hom
      rw [Category.comp_id, Category.id_comp])

/-- Ordinary global sections of equivariant coefficients with the action
supplied by the compatible-coefficient section diagram. -/
def pullbackSectionsFunctor :
    EquivariantSheaf R ρ ⥤ Action (ModuleCat.{u} R) G :=
  ofEquivariantFunctor R ρ ⋙ CoefficientDiagram.sectionsFunctor ⋙
    (Action.functorCategoryEquivalence (ModuleCat.{u} R) G).inverse

/-- On coefficients, the section-action functor acts by ordinary sections. -/
theorem pullbackSectionsFunctor_map_hom {F E : EquivariantSheaf R ρ} (f : F ⟶ E) :
    (pullbackSectionsFunctor R ρ |>.map f).hom =
      (EtaleDerivedSections.sections Y R).map f.hom :=
  CoefficientDiagram.sectionsFunctor_map_app
    ((ofEquivariantFunctor R ρ).map f) (SingleObj.star G)

/-- Every group element acts on sections by geometric restriction followed
by its coefficient structure map. -/
theorem pullbackSectionsFunctor_obj_ρ (F : EquivariantSheaf R ρ) (g : G) :
    ((pullbackSectionsFunctor R ρ).obj F).ρ g =
      (sectionsMap (aut ρ g).hom R).app F.obj ≫
        (EtaleDerivedSections.sections Y R).map (F.act g) :=
  CoefficientDiagram.sections_map (ofEquivariant R ρ F) g

/-- Degree-zero cohomology agrees with ordinary sections, naturally in
equivariant coefficients and equivariantly for the scheme action. -/
def pullbackCohomologyZeroFunctorIso :
    pullbackCohomologyFunctor R ρ 0 ≅ pullbackSectionsFunctor R ρ :=
  (Functor.isoWhiskerLeft (pullbackCohomologyFunctor R ρ 0)
    (Action.functorCategoryEquivalence (ModuleCat.{u} R) G).unitIso) ≪≫
  (Functor.isoWhiskerRight (ofEquivariantCohomologyFunctorIso R ρ 0).symm
    (Action.functorCategoryEquivalence (ModuleCat.{u} R) G).inverse) ≪≫
  (Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (ofEquivariantFunctor R ρ)
      CoefficientDiagram.cohomologyZeroFunctorIso)
    (Action.functorCategoryEquivalence (ModuleCat.{u} R) G).inverse)

/-- The equivariant degree-zero identification has the usual canonical
cohomology-to-sections map as its underlying component. -/
theorem pullbackCohomologyZeroFunctorIso_hom_app_hom (F : EquivariantSheaf R ρ) :
    ((pullbackCohomologyZeroFunctorIso R ρ).hom.app F).hom =
      (EtaleDerivedSections.cohomologyZeroIso Y R).hom.app F.obj := by
  change 𝟙 _ ≫ 𝟙 _ ≫ (EtaleDerivedSections.cohomologyZeroIso Y R).hom.app F.obj = _
  simp only [Category.id_comp]

end Langlands.Geometry.EtaleCohomologyAction
