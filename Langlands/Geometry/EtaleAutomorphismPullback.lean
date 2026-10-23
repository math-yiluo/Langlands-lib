import Langlands.Geometry.EtaleCohomologyAction
import Langlands.Geometry.EtaleDerivedPullbackFunctoriality

/-!
# Comparing automorphism translation with étale pullback
-/

noncomputable section

namespace Langlands.Geometry.EtalePullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Langlands.Cohomology

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} (A : Type*) [Category A]

/-- Étale restriction along an automorphism is its existing sheaf translation. -/
def restrictionAutomorphismIso (σ : Y ≅ Y) :
    restriction σ.hom A ≅ EtaleAutomorphism.translate A σ :=
  Iso.refl _

/-- On terminal-object sections, restriction along an automorphism is the
inverse of its translation comparison. -/
theorem terminalSectionsMap_automorphism (σ : Y ≅ Y)
    (F : Sheaf Y.smallEtaleTopology A) :
    (terminalSectionsMap σ.hom A).app F =
      (EtaleAutomorphism.sectionsIso A σ).inv.app F := by
  dsimp [terminalSectionsMap, EtaleAutomorphism.sectionsIso]
  congr 1

variable (R : Type u) [CommRing R]

/-- The ordinary-section pullback is the translation comparison conjugated
by the canonical identification with terminal-object sections. -/
theorem sectionsMap_automorphism (σ : Y ≅ Y)
    (F : EtaleDerivedSections.ModuleSheaf Y R) :
    (sectionsMap σ.hom R).app F =
      (EtaleDerivedSections.sectionsIso Y R).hom.app F ≫
        (EtaleAutomorphism.sectionsIso (ModuleCat.{u} R) σ).inv.app F ≫
        (EtaleDerivedSections.sectionsIso Y R).inv.app
          ((restriction σ.hom (ModuleCat.{u} R)).obj F) := by
  dsimp only [sectionsMap, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [terminalSectionsMap_automorphism]

end Langlands.Geometry.EtalePullback

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} (R : Type u) [CommRing R]
variable {G : Type w} [Group G] (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- The pullback chain map followed by the lift of the equivariant coefficient
map, computed using ordinary global sections. -/
def pullbackActionChainMap (F : EquivariantSheaf R ρ) (g : G)
    (I : InjectiveResolution F.obj) :
    ((EtaleDerivedSections.sections Y R).mapHomologicalComplex _).obj I.cocomplex ⟶
      ((EtaleDerivedSections.sections Y R).mapHomologicalComplex _).obj I.cocomplex :=
  resolutionSectionsMap (aut ρ g).hom R I ≫
    ((EtaleDerivedSections.sections Y R).mapHomologicalComplex _).map
      (TranslationAction.lift F g I)

/-- The canonical comparison of section complexes intertwines translation
and pullback with equivariant coefficients. -/
theorem pullbackActionChainMap_comm (F : EquivariantSheaf R ρ) (g : G)
    (I : InjectiveResolution F.obj) :
    TranslationAction.chainMap (sectionsTop R) F g I ≫
        (NatIso.mapHomologicalComplex (EtaleDerivedSections.sectionsIso Y R) _).inv.app
          I.cocomplex =
      (NatIso.mapHomologicalComplex (EtaleDerivedSections.sectionsIso Y R) _).inv.app
          I.cocomplex ≫ pullbackActionChainMap R ρ F g I := by
  ext n : 1
  simp only [pullbackActionChainMap, TranslationAction.chainMap,
    HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
    Functor.mapHomologicalComplex_map_f, resolutionSectionsMap,
    NatTrans.mapHomologicalComplex_app_f, sectionsMap_automorphism, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  exact congrArg (fun t =>
    (EtaleAutomorphism.sectionsIso (ModuleCat.{u} R) (aut ρ g)).inv.app
      (I.cocomplex.X n) ≫ t)
    ((EtaleDerivedSections.sectionsIso Y R).inv.naturality
      ((TranslationAction.lift F g I).f n))

/-- Pullback with an equivariant coefficient map is computed by the
corresponding pullback chain map on any injective resolution. -/
theorem pullbackActionChainMap_cohomology (F : EquivariantSheaf R ρ) (g : G)
    (I : InjectiveResolution F.obj) (q : ℕ) :
    cohomologyMapWithCoefficients (aut ρ g).hom R q (F.act g) =
      (I.isoRightDerivedObj (EtaleDerivedSections.sections Y R) q).hom ≫
        (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map
          (pullbackActionChainMap R ρ F g I) ≫
        (I.isoRightDerivedObj (EtaleDerivedSections.sections Y R) q).inv := by
  apply cohomologyMapWithCoefficients_ofResolutions
  rw [DerivedComparison.mapInjectiveResolution_ι_f_zero]
  exact TranslationAction.lift_comm_zero F g I

/-- The canonical comparison with right-derived sections intertwines the
existing translation action with geometric pullback and the coefficient map. -/
theorem cohomologyIso_comm (F : EquivariantSheaf R ρ) (q : ℕ) (g : G) :
    TranslationAction.homologyAction (sectionsTop R) F (injectiveResolution F.obj) q g ≫
        (cohomologyIso R ρ F q).hom =
      (cohomologyIso R ρ F q).hom ≫
        cohomologyMapWithCoefficients (aut ρ g).hom R q (F.act g) := by
  let I := injectiveResolution F.obj
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q
  let η := NatIso.mapHomologicalComplex (EtaleDerivedSections.sectionsIso Y R)
    (ComplexShape.up ℕ)
  let e := I.isoRightDerivedObj (EtaleDerivedSections.sections Y R) q
  have hc : H.map (TranslationAction.chainMap (sectionsTop R) F g I) ≫
      H.map (η.inv.app I.cocomplex) =
      H.map (η.inv.app I.cocomplex) ≫
        H.map (pullbackActionChainMap R ρ F g I) := by
    simpa only [Functor.map_comp] using
      congrArg H.map (pullbackActionChainMap_comm R ρ F g I)
  rw [pullbackActionChainMap_cohomology R ρ F g I]
  change H.map (TranslationAction.chainMap (sectionsTop R) F g I) ≫
      (H.map (η.inv.app I.cocomplex) ≫ e.inv) =
    (H.map (η.inv.app I.cocomplex) ≫ e.inv) ≫
      (e.hom ≫ H.map (pullbackActionChainMap R ρ F g I) ≫ e.inv)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ e.inv) hc).trans (Category.assoc _ _ _))

/-- The geometric action on the published right-derived cohomology module. -/
def pullbackCohomologyAction (F : EquivariantSheaf R ρ) (q : ℕ) :
    Action (ModuleCat.{u} R) G where
  V := (EtaleDerivedSections.cohomology Y R q).obj F.obj
  ρ := (cohomologyIso R ρ F q).conj.toMonoidHom.comp
    (TranslationAction.homologyAction (sectionsTop R) F (injectiveResolution F.obj) q)

/-- Each group element acts by geometric pullback followed by its coefficient
structure map. -/
theorem pullbackCohomologyAction_ρ (F : EquivariantSheaf R ρ) (q : ℕ) (g : G) :
    (pullbackCohomologyAction R ρ F q).ρ g =
      cohomologyMapWithCoefficients (aut ρ g).hom R q (F.act g) := by
  change (cohomologyIso R ρ F q).inv ≫
    (TranslationAction.homologyAction (sectionsTop R) F (injectiveResolution F.obj) q g ≫
      (cohomologyIso R ρ F q).hom) = _
  rw [cohomologyIso_comm]
  simp only [Iso.inv_hom_id_assoc]

/-- The canonical cohomology comparison as an isomorphism of group actions. -/
def pullbackCohomologyActionIso (F : EquivariantSheaf R ρ) (q : ℕ) :
    TranslationAction.cohomologyAction (sectionsTop R) F (injectiveResolution F.obj) q ≅
      pullbackCohomologyAction R ρ F q :=
  Action.mkIso (cohomologyIso R ρ F q) fun g => by
    rw [pullbackCohomologyAction_ρ]
    exact cohomologyIso_comm R ρ F q g

end Langlands.Geometry.EtaleCohomologyAction
