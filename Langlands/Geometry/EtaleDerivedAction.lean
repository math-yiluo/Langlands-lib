import Langlands.Geometry.EtaleDerivedDiagram
import Langlands.Geometry.EtaleActionFunctor

/-! # Geometric group actions on bounded-below derived etale sections -/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u w wS wT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {Y : Scheme.{u}} (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf Y R)]
  [HasDerivedCategory.{wT} (ModuleCat.{u} R)]
variable {G : Type w} [Group G] (ρ : G →* (Aut Y)ᵐᵒᵖ)

/-- Derived global sections with the geometric group action, functorially in
actual equivariant small-etale coefficient sheaves. -/
def pullbackDerivedSectionsFunctor :
    EquivariantSheaf R ρ ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G := by
  letI : ∀ i : SingleObj G, HasDerivedCategory.{wS}
      (EtaleDerivedSections.ModuleSheaf ((actionSchemeDiagram ρ).obj i).unop R) :=
    fun _ => inferInstanceAs (HasDerivedCategory.{wS} (EtaleDerivedSections.ModuleSheaf Y R))
  exact ofEquivariantFunctor R ρ ⋙ CoefficientDiagram.derivedSectionsFunctor ⋙
    (Action.functorCategoryEquivalence (DerivedCategory.Plus (ModuleCat.{u} R)) G).inverse

/-- The underlying coefficient map is the actual derived-section map. -/
@[simp] theorem pullbackDerivedSectionsFunctor_map_hom {F E : EquivariantSheaf R ρ}
    (f : F ⟶ E) :
    ((pullbackDerivedSectionsFunctor R ρ).map f).hom =
      (EtaleDerivedSectionsPlus.derivedSections Y R).map f.hom := rfl

/-- Each group element acts by derived geometric pullback followed by the
derived map of its coefficient structure morphism. -/
theorem pullbackDerivedSectionsFunctor_obj_ρ (F : EquivariantSheaf R ρ) (g : G) :
    ((pullbackDerivedSectionsFunctor R ρ).obj F).ρ g =
      (EtalePullback.derivedSectionsMap (aut ρ g).hom R).app F.obj ≫
        (EtaleDerivedSectionsPlus.derivedSections Y R).map (F.act g) := rfl

/-- The cohomology of the actual derived action is the existing geometric
action on ordinary cohomology. -/
def pullbackDerivedHomologyIso (F : EquivariantSheaf R ρ) (q : ℕ) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G).obj
        ((pullbackDerivedSectionsFunctor R ρ).obj F) ≅
      pullbackCohomologyAction R ρ F q :=
  Action.mkIso ((EtaleDerivedSectionsPlus.homologyNatIso Y R q).app F.obj)
    (fun g => by
      change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).map
          (derivedSectionsMapWithCoefficients (aut ρ g).hom R (F.act g)) ≫
          (EtaleDerivedSectionsPlus.homologyNatIso Y R q).hom.app F.obj =
        (EtaleDerivedSectionsPlus.homologyNatIso Y R q).hom.app F.obj ≫
          (pullbackCohomologyAction R ρ F q).ρ g
      rw [pullbackCohomologyAction_ρ]
      exact derivedSectionsMapWithCoefficients_homology (aut ρ g).hom R (F.act g) q)

/-- The recovery of ordinary cohomology actions is natural in equivariant
coefficient morphisms. -/
def pullbackDerivedHomologyFunctorIso (q : ℕ) :
    pullbackDerivedSectionsFunctor R ρ ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G ≅
      pullbackCohomologyFunctor R ρ q :=
  NatIso.ofComponents (fun F => pullbackDerivedHomologyIso R ρ F q)
    (fun {F E} f => by
      apply Action.Hom.ext
      exact (EtaleDerivedSectionsPlus.homologyNatIso Y R q).hom.naturality f.hom)

/-- The equivariant cohomology comparison is the canonical comparison on
the underlying module. -/
@[simp] theorem pullbackDerivedHomologyIso_hom_hom
    (F : EquivariantSheaf R ρ) (q : ℕ) :
    (pullbackDerivedHomologyIso R ρ F q).hom.hom =
      (EtaleDerivedSectionsPlus.homologyNatIso Y R q).hom.app F.obj := rfl

/-- Degree-zero cohomology of the actual derived action is the ordinary
section action, naturally in equivariant coefficients. -/
def pullbackDerivedZeroFunctorIso :
    pullbackDerivedSectionsFunctor R ρ ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G ≅
      pullbackSectionsFunctor R ρ :=
  pullbackDerivedHomologyFunctorIso R ρ 0 ≪≫ pullbackCohomologyZeroFunctorIso R ρ

/-- The equivariant degree-zero comparison has the canonical
derived-cohomology-to-sections component. -/
theorem pullbackDerivedZeroFunctorIso_hom_app_hom (F : EquivariantSheaf R ρ) :
    ((pullbackDerivedZeroFunctorIso R ρ).hom.app F).hom =
      (EtaleDerivedSectionsPlus.homologyZeroIso Y R).hom.app F.obj := by
  change (EtaleDerivedSectionsPlus.homologyNatIso Y R 0).hom.app F.obj ≫
    ((pullbackCohomologyZeroFunctorIso R ρ).hom.app F).hom = _
  rw [pullbackCohomologyZeroFunctorIso_hom_app_hom]
  rfl

end Langlands.Geometry.EtaleCohomologyAction
