import Langlands.Geometry.EtaleDerivedAction
import Langlands.Geometry.EtaleEquivariantPullbackCoherence

/-! # Equivariant geometric maps on bounded-below derived etale sections -/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u w wX wY wZ wT

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (R : Type u) [CommRing R]
variable [HasDerivedCategory.{wX} (EtaleDerivedSections.ModuleSheaf X R)]
  [HasDerivedCategory.{wY} (EtaleDerivedSections.ModuleSheaf Y R)]
  [HasDerivedCategory.{wT} (ModuleCat.{u} R)]
variable {G : Type w} [Group G]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (τ : G →* (Aut Y)ᵐᵒᵖ)
variable (f : Y ⟶ X) [Etale f]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)

namespace GeometricCoefficientMap

variable {R ρ τ f hf}
variable {F : EquivariantSheaf R ρ} {E : EquivariantSheaf R τ}

/-- A geometric coefficient map induces an equivariant morphism of actual
bounded-below derived-section objects. -/
def derivedSectionsMap (α : GeometricCoefficientMap R ρ τ f hf F E) :
    (pullbackDerivedSectionsFunctor R ρ).obj F ⟶
      (pullbackDerivedSectionsFunctor R τ).obj E where
  hom := derivedSectionsMapWithCoefficients f R α.hom
  comm g := by
    change derivedSectionsMapWithCoefficients (aut ρ g).hom R (F.act g) ≫
        derivedSectionsMapWithCoefficients f R α.hom =
      derivedSectionsMapWithCoefficients f R α.hom ≫
        derivedSectionsMapWithCoefficients (aut τ g).hom R (E.act g)
    rw [derivedSectionsMapWithCoefficients_comp,
      derivedSectionsMapWithCoefficients_comp, α.comp_coefficient g]
    dsimp only [derivedSectionsMapWithCoefficients]
    rw [Functor.map_comp, ← Category.assoc, EtalePullback.derivedSectionsMap_congr]
    rfl

/-- Forgetting equivariance gives the specified geometric derived pullback
followed by the actual coefficient morphism. -/
@[simp] theorem derivedSectionsMap_hom
    (α : GeometricCoefficientMap R ρ τ f hf F E) :
    α.derivedSectionsMap.hom = derivedSectionsMapWithCoefficients f R α.hom := rfl

/-- The derived geometric construction respects a source coefficient map. -/
theorem derivedSectionsMap_precomp {F' : EquivariantSheaf R ρ}
    (α : GeometricCoefficientMap R ρ τ f hf F E) (β : F' ⟶ F) :
    (α.precomp β).derivedSectionsMap =
      (pullbackDerivedSectionsFunctor R ρ).map β ≫ α.derivedSectionsMap := by
  apply Action.Hom.ext
  change derivedSectionsMapWithCoefficients f R
      ((restriction f (ModuleCat.{u} R)).map β.hom ≫ α.hom) =
    (EtaleDerivedSectionsPlus.derivedSections X R).map β.hom ≫
      derivedSectionsMapWithCoefficients f R α.hom
  dsimp only [derivedSectionsMapWithCoefficients]
  rw [Functor.map_comp, ← Category.assoc]
  simpa only [Category.assoc, Functor.comp_map] using congrArg
    (fun k => k ≫ (EtaleDerivedSectionsPlus.derivedSections Y R).map α.hom)
    ((EtalePullback.derivedSectionsMap f R).naturality β.hom).symm

/-- The derived geometric construction respects a target coefficient map. -/
theorem derivedSectionsMap_postcomp {E' : EquivariantSheaf R τ}
    (α : GeometricCoefficientMap R ρ τ f hf F E) (β : E ⟶ E') :
    (α.postcomp β).derivedSectionsMap =
      α.derivedSectionsMap ≫ (pullbackDerivedSectionsFunctor R τ).map β := by
  apply Action.Hom.ext
  change derivedSectionsMapWithCoefficients f R (α.hom ≫ β.hom) =
    derivedSectionsMapWithCoefficients f R α.hom ≫
      (EtaleDerivedSectionsPlus.derivedSections Y R).map β.hom
  simp only [derivedSectionsMapWithCoefficients, Functor.map_comp, Category.assoc]

/-- The canonical homology comparison identifies the derived equivariant map
with the previously constructed ordinary cohomology map. -/
theorem derivedSectionsMap_homology
    (α : GeometricCoefficientMap R ρ τ f hf F E) (q : ℕ) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G).map
        α.derivedSectionsMap ≫ (pullbackDerivedHomologyIso R τ E q).hom =
      (pullbackDerivedHomologyIso R ρ F q).hom ≫ α.cohomologyMap q := by
  apply Action.Hom.ext
  exact derivedSectionsMapWithCoefficients_homology f R α.hom q

/-- Degree-zero cohomology of the derived equivariant map is the existing
geometric restriction on sections. -/
theorem derivedSectionsMap_zero
    (α : GeometricCoefficientMap R ρ τ f hf F E) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G).map
        α.derivedSectionsMap ≫ (pullbackDerivedZeroFunctorIso R τ).hom.app E =
      (pullbackDerivedZeroFunctorIso R ρ).hom.app F ≫ α.sectionsMap := by
  change _ ≫ ((pullbackDerivedHomologyIso R τ E 0).hom ≫
      (pullbackCohomologyZeroFunctorIso R τ).hom.app E) =
    ((pullbackDerivedHomologyIso R ρ F 0).hom ≫
      (pullbackCohomologyZeroFunctorIso R ρ).hom.app F) ≫ α.sectionsMap
  erw [← Category.assoc, α.derivedSectionsMap_homology 0,
    Category.assoc, α.cohomologyMap_zero, ← Category.assoc]

end GeometricCoefficientMap

/-- Derived pullback along an equivariant etale map is natural in actual
equivariant coefficient sheaves. -/
def equivariantPullbackDerivedSections :
    pullbackDerivedSectionsFunctor R ρ ⟶
      equivariantPullback R ρ τ f hf ⋙ pullbackDerivedSectionsFunctor R τ where
  app F := (equivariantPullbackCoefficient R ρ τ f hf F).derivedSectionsMap
  naturality {F E} β := by
    apply Action.Hom.ext
    change (EtaleDerivedSectionsPlus.derivedSections X R).map β.hom ≫
        derivedSectionsMapWithCoefficients f R (𝟙 _) =
      derivedSectionsMapWithCoefficients f R (𝟙 _) ≫
        (EtaleDerivedSectionsPlus.derivedSections Y R).map
          ((restriction f (ModuleCat.{u} R)).map β.hom)
    dsimp only [derivedSectionsMapWithCoefficients]
    erw [(EtaleDerivedSectionsPlus.derivedSections Y R).map_id,
      (EtaleDerivedSectionsPlus.derivedSections Y R).map_id]
    erw [Category.comp_id, Category.comp_id]
    exact (EtalePullback.derivedSectionsMap f R).naturality β.hom

/-- The underlying map is precisely actual geometric pullback in D⁺. -/
@[simp] theorem equivariantPullbackDerivedSections_app_hom (F : EquivariantSheaf R ρ) :
    ((equivariantPullbackDerivedSections R ρ τ f hf).app F).hom =
      (EtalePullback.derivedSectionsMap f R).app F.obj := by
  change derivedSectionsMapWithCoefficients f R (𝟙 _) = _
  dsimp only [derivedSectionsMapWithCoefficients]
  erw [(EtaleDerivedSectionsPlus.derivedSections Y R).map_id]
  exact Category.comp_id _

/-- The equivariant canonical homology comparison commutes with geometric
derived pullback. -/
theorem equivariantPullbackDerivedSections_homology
    (F : EquivariantSheaf R ρ) (q : ℕ) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) q).mapAction G).map
        ((equivariantPullbackDerivedSections R ρ τ f hf).app F) ≫
        (pullbackDerivedHomologyIso R τ
          ((equivariantPullback R ρ τ f hf).obj F) q).hom =
      (pullbackDerivedHomologyIso R ρ F q).hom ≫
        (equivariantPullbackCohomology R ρ τ f hf q).app F :=
  (equivariantPullbackCoefficient R ρ τ f hf F).derivedSectionsMap_homology q

/-- The degree-zero comparison commutes with equivariant derived pullback. -/
theorem equivariantPullbackDerivedSections_zero (F : EquivariantSheaf R ρ) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G).map
        ((equivariantPullbackDerivedSections R ρ τ f hf).app F) ≫
        (pullbackDerivedZeroFunctorIso R τ).hom.app
          ((equivariantPullback R ρ τ f hf).obj F) =
      (pullbackDerivedZeroFunctorIso R ρ).hom.app F ≫
        (equivariantPullbackSections R ρ τ f hf).app F :=
  (equivariantPullbackCoefficient R ρ τ f hf F).derivedSectionsMap_zero

set_option maxHeartbeats 800000 in
/-- Derived equivariant pullback along the identity is the identity after the
canonical identity restriction comparison. -/
theorem equivariantPullbackDerivedSections_id (F : EquivariantSheaf R ρ) :
    (equivariantPullbackDerivedSections R ρ ρ (𝟙 X) (equivariantMap_id ρ)).app F ≫
        (pullbackDerivedSectionsFunctor R ρ).map
          (X := (equivariantPullback R ρ ρ (𝟙 X) (equivariantMap_id ρ)).obj F) (Y := F)
          ((equivariantPullbackId R ρ).hom.app F) =
      𝟙 ((pullbackDerivedSectionsFunctor R ρ).obj F) := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, equivariantPullbackDerivedSections_app_hom,
    pullbackDerivedSectionsFunctor_map_hom, equivariantPullbackId_hom_app_hom,
    Action.id_hom]
  change (EtalePullback.derivedSectionsMap (𝟙 X) R).app F.obj ≫
      (EtaleDerivedSectionsPlus.derivedSections X R).map
        ((restrictionId (ModuleCat.{u} R)).hom.app F.obj) =
    𝟙 ((EtaleDerivedSectionsPlus.derivedSections X R).obj F.obj)
  exact EtalePullback.derivedSectionsMap_id R F.obj

/-- Derived equivariant pullback respects equality of the scheme map. -/
theorem equivariantPullbackDerivedSections_congr {k : Y ⟶ X} [Etale k]
    (hk : ∀ g, k ≫ (aut ρ g).hom = (aut τ g).hom ≫ k)
    (h : f = k) (F : EquivariantSheaf R ρ) :
    (equivariantPullbackDerivedSections R ρ τ f hf).app F ≫
        (pullbackDerivedSectionsFunctor R τ).map
          ((equivariantPullbackCongr R ρ τ hf hk h).hom.app F) =
      (equivariantPullbackDerivedSections R ρ τ k hk).app F := by
  subst k
  simp [equivariantPullbackCongr]

variable {Z : Scheme.{u}}
variable [HasDerivedCategory.{wZ} (EtaleDerivedSections.ModuleSheaf Z R)]
variable (υ : G →* (Aut Z)ᵐᵒᵖ) (g : Z ⟶ Y) [Etale g]
variable (hg : ∀ a, g ≫ (aut τ a).hom = (aut υ a).hom ≫ g)

/-- Derived equivariant pullbacks compose after the canonical comparison
between successive and composite coefficient restrictions. -/
theorem equivariantPullbackDerivedSections_comp (F : EquivariantSheaf R ρ) :
    (equivariantPullbackDerivedSections R ρ τ f hf).app F ≫
        (equivariantPullbackDerivedSections R τ υ g hg).app
          ((equivariantPullback R ρ τ f hf).obj F) ≫
        (pullbackDerivedSectionsFunctor R υ).map
          ((equivariantPullbackComp R ρ τ υ f g hf hg).hom.app F) =
      (equivariantPullbackDerivedSections R ρ υ (g ≫ f)
        (equivariantMap_comp ρ τ υ f g hf hg)).app F := by
  apply Action.Hom.ext
  simp only [Action.comp_hom, equivariantPullbackDerivedSections_app_hom,
    pullbackDerivedSectionsFunctor_map_hom, equivariantPullbackComp_hom_app_hom]
  change (EtalePullback.derivedSectionsMap f R).app F.obj ≫
      (EtalePullback.derivedSectionsMap g R).app
        ((restriction f (ModuleCat.{u} R)).obj F.obj) ≫
      (EtaleDerivedSectionsPlus.derivedSections Z R).map
        ((restrictionComp f (ModuleCat.{u} R) g).hom.app F.obj) =
    (EtalePullback.derivedSectionsMap (g ≫ f) R).app F.obj
  exact EtalePullback.derivedSectionsMap_comp f R g F.obj

end Langlands.Geometry.EtaleCohomologyAction
