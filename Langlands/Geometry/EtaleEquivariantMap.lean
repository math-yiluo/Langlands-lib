import Langlands.Geometry.EtaleActionFunctor

/-!
# Geometric maps on equivariant ordinary étale cohomology
-/

noncomputable section

namespace Langlands.Geometry.EtaleCohomologyAction

open CategoryTheory AlgebraicGeometry
open Langlands.Cohomology EtalePullback

universe u w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y : Scheme.{u}} (R : Type u) [CommRing R]
variable {G : Type w} [Group G]
variable (ρ : G →* (Aut X)ᵐᵒᵖ) (τ : G →* (Aut Y)ᵐᵒᵖ)
variable (f : Y ⟶ X) [Etale f]
variable (hf : ∀ g, f ≫ (aut ρ g).hom = (aut τ g).hom ≫ f)

/-- The restriction comparison supplied by a commuting geometric action square. -/
def equivariantRestrictionIso (g : G) :
    translateBy R ρ g ⋙ restriction f (ModuleCat.{u} R) ≅
      restriction f (ModuleCat.{u} R) ⋙ translateBy R τ g :=
  restrictionComp (aut ρ g).hom (ModuleCat.{u} R) f ≪≫
    restrictionCongr R (hf g) ≪≫
    (restrictionComp f (ModuleCat.{u} R) (aut τ g).hom).symm

/-- An actual coefficient-sheaf map compatible with an equivariant étale map.
The compatibility equation concerns sheaves, not cohomology. -/
@[ext] structure GeometricCoefficientMap
    (F : EquivariantSheaf R ρ) (E : EquivariantSheaf R τ) where
  hom : (restriction f (ModuleCat.{u} R)).obj F.obj ⟶ E.obj
  comm (g : G) :
    (restriction f (ModuleCat.{u} R)).map (F.act g) ≫ hom =
      (equivariantRestrictionIso R ρ τ f hf g).hom.app F.obj ≫
        (translateBy R τ g).map hom ≫ E.act g

namespace GeometricCoefficientMap

variable {R ρ τ f hf}
variable {F : EquivariantSheaf R ρ} {E : EquivariantSheaf R τ}

/-- The coefficient square after identifying both composite restriction functors. -/
theorem comp_coefficient (α : GeometricCoefficientMap R ρ τ f hf F E) (g : G) :
    (restrictionComp (aut ρ g).hom (ModuleCat.{u} R) f).inv.app F.obj ≫
      (restriction f (ModuleCat.{u} R)).map (F.act g) ≫ α.hom =
    (restrictionCongr R (hf g)).hom.app F.obj ≫
      (restrictionComp f (ModuleCat.{u} R) (aut τ g).hom).inv.app F.obj ≫
        (translateBy R τ g).map α.hom ≫ E.act g := by
  rw [α.comm]
  dsimp only [equivariantRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The geometric pullback and coefficient map induce a map of cohomology actions. -/
def cohomologyMap (α : GeometricCoefficientMap R ρ τ f hf F E) (q : ℕ) :
    pullbackCohomologyAction R ρ F q ⟶ pullbackCohomologyAction R τ E q where
  hom := cohomologyMapWithCoefficients f R q α.hom
  comm g := by
    rw [pullbackCohomologyAction_ρ, pullbackCohomologyAction_ρ,
      cohomologyMapWithCoefficients_comp, cohomologyMapWithCoefficients_comp,
      α.comp_coefficient g]
    dsimp only [cohomologyMapWithCoefficients]
    rw [Functor.map_comp, ← Category.assoc, EtalePullback.cohomologyMap_congr]
    rfl

/-- The underlying equivariant map is the constructed ordinary cohomology map. -/
@[simp] theorem cohomologyMap_hom
    (α : GeometricCoefficientMap R ρ τ f hf F E) (q : ℕ) :
    (α.cohomologyMap q).hom = cohomologyMapWithCoefficients f R q α.hom := rfl

/-- Precompose the coefficient map with an equivariant map on the source scheme. -/
def precomp {F' : EquivariantSheaf R ρ}
    (α : GeometricCoefficientMap R ρ τ f hf F E) (β : F' ⟶ F) :
    GeometricCoefficientMap R ρ τ f hf F' E where
  hom := (restriction f (ModuleCat.{u} R)).map β.hom ≫ α.hom
  comm g := by
    rw [← Category.assoc, ← Functor.map_comp, β.comm, Functor.map_comp,
      Category.assoc, α.comm]
    have h := (equivariantRestrictionIso R ρ τ f hf g).hom.naturality β.hom
    dsimp only [Functor.comp_map] at h
    rw [← Category.assoc, ← Category.assoc, h]
    simp only [Functor.map_comp, Category.assoc]

/-- Postcompose the coefficient map with an equivariant map on the target scheme. -/
def postcomp {E' : EquivariantSheaf R τ}
    (α : GeometricCoefficientMap R ρ τ f hf F E) (β : E ⟶ E') :
    GeometricCoefficientMap R ρ τ f hf F E' where
  hom := α.hom ≫ β.hom
  comm g := by
    rw [← Category.assoc, α.comm]
    simp only [Category.assoc]
    rw [β.comm, Functor.map_comp]
    simp only [Category.assoc]

/-- The cohomology construction respects a source coefficient morphism. -/
theorem cohomologyMap_precomp {F' : EquivariantSheaf R ρ}
    (α : GeometricCoefficientMap R ρ τ f hf F E) (β : F' ⟶ F) (q : ℕ) :
    (α.precomp β).cohomologyMap q =
      (pullbackCohomologyFunctor R ρ q).map β ≫ α.cohomologyMap q := by
  apply Action.Hom.ext
  change cohomologyMapWithCoefficients f R q
    ((restriction f (ModuleCat.{u} R)).map β.hom ≫ α.hom) =
      (EtaleDerivedSections.cohomology X R q).map β.hom ≫
        cohomologyMapWithCoefficients f R q α.hom
  dsimp only [cohomologyMapWithCoefficients]
  rw [Functor.map_comp, ← Category.assoc]
  exact congrArg (fun k => k ≫ (EtaleDerivedSections.cohomology Y R q).map α.hom)
    ((EtalePullback.cohomologyMap f R q).naturality β.hom).symm

/-- The cohomology construction respects a target coefficient morphism. -/
theorem cohomologyMap_postcomp {E' : EquivariantSheaf R τ}
    (α : GeometricCoefficientMap R ρ τ f hf F E) (β : E ⟶ E') (q : ℕ) :
    (α.postcomp β).cohomologyMap q =
      α.cohomologyMap q ≫ (pullbackCohomologyFunctor R τ q).map β := by
  apply Action.Hom.ext
  change cohomologyMapWithCoefficients f R q (α.hom ≫ β.hom) =
    cohomologyMapWithCoefficients f R q α.hom ≫
      (EtaleDerivedSections.cohomology Y R q).map β.hom
  simp only [cohomologyMapWithCoefficients, Functor.map_comp, Category.assoc]

/-- The section map with its geometric action, via the canonical degree-zero comparison. -/
def sectionsMap (α : GeometricCoefficientMap R ρ τ f hf F E) :
    (pullbackSectionsFunctor R ρ).obj F ⟶ (pullbackSectionsFunctor R τ).obj E :=
  (pullbackCohomologyZeroFunctorIso R ρ).inv.app F ≫
    α.cohomologyMap 0 ≫ (pullbackCohomologyZeroFunctorIso R τ).hom.app E

/-- The cohomology-to-sections comparison commutes with the geometric map. -/
theorem cohomologyMap_zero (α : GeometricCoefficientMap R ρ τ f hf F E) :
    α.cohomologyMap 0 ≫ (pullbackCohomologyZeroFunctorIso R τ).hom.app E =
      (pullbackCohomologyZeroFunctorIso R ρ).hom.app F ≫ α.sectionsMap := by
  simp only [sectionsMap, Iso.hom_inv_id_app_assoc]

/-- On ordinary sections this is restriction followed by the coefficient map. -/
theorem sectionsMap_hom (α : GeometricCoefficientMap R ρ τ f hf F E) :
    α.sectionsMap.hom =
      (EtalePullback.sectionsMap f R).app F.obj ≫
        (EtaleDerivedSections.sections Y R).map α.hom := by
  apply (cancel_epi ((EtaleDerivedSections.cohomologyZeroIso X R).hom.app F.obj)).1
  have h := congrArg (fun φ => φ.hom) α.cohomologyMap_zero
  simp only [Action.comp_hom, cohomologyMap_hom,
    pullbackCohomologyZeroFunctorIso_hom_app_hom] at h
  rw [← h]
  dsimp only [cohomologyMapWithCoefficients]
  rw [Category.assoc, (EtaleDerivedSections.cohomologyZeroIso Y R).hom.naturality,
    ← Category.assoc, EtalePullback.cohomologyMap_zero, Category.assoc]

/-- The section construction respects a source coefficient morphism. -/
theorem sectionsMap_precomp {F' : EquivariantSheaf R ρ}
    (α : GeometricCoefficientMap R ρ τ f hf F E) (β : F' ⟶ F) :
    (α.precomp β).sectionsMap =
      (pullbackSectionsFunctor R ρ).map β ≫ α.sectionsMap := by
  apply Action.Hom.ext
  rw [Action.comp_hom, sectionsMap_hom, sectionsMap_hom,
    pullbackSectionsFunctor_map_hom]
  change (EtalePullback.sectionsMap f R).app F'.obj ≫
    (EtaleDerivedSections.sections Y R).map
      ((restriction f (ModuleCat.{u} R)).map β.hom ≫ α.hom) = _
  rw [Functor.map_comp, ← Category.assoc]
  exact congrArg (fun k => k ≫ (EtaleDerivedSections.sections Y R).map α.hom)
    ((EtalePullback.sectionsMap f R).naturality β.hom).symm

/-- The section construction respects a target coefficient morphism. -/
theorem sectionsMap_postcomp {E' : EquivariantSheaf R τ}
    (α : GeometricCoefficientMap R ρ τ f hf F E) (β : E ⟶ E') :
    (α.postcomp β).sectionsMap =
      α.sectionsMap ≫ (pullbackSectionsFunctor R τ).map β := by
  apply Action.Hom.ext
  rw [Action.comp_hom, sectionsMap_hom, sectionsMap_hom,
    pullbackSectionsFunctor_map_hom]
  change (EtalePullback.sectionsMap f R).app F.obj ≫
    (EtaleDerivedSections.sections Y R).map (α.hom ≫ β.hom) = _
  rw [Functor.map_comp, Category.assoc]

end GeometricCoefficientMap

end Langlands.Geometry.EtaleCohomologyAction
