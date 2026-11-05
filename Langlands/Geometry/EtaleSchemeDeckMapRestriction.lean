import Langlands.Geometry.EtaleSchemeDeckRestriction

/-! # Restriction comparison for maps of original deck geometries -/

noncomputable section

universe u t wY wR

set_option autoImplicit false

namespace Langlands.Geometry.EtaleSchemeDeckAction

open CategoryTheory AlgebraicGeometry
open EtaleInverseImage EtaleDerivedSections EtaleCohomologyAction
open EtalePullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z : Scheme.{u}} {G : Type t} [Group G]
variable {τ : G →* (Aut Y)ᵐᵒᵖ} {σ : G →* (Aut Z)ᵐᵒᵖ}
variable {p : Y ⟶ X} [Etale p] {q : Z ⟶ X} [Etale q]
variable {hp : ∀ g, (aut τ g).hom ≫ p = p}
variable {hq : ∀ g, (aut σ g).hom ≫ q = q}
variable (R : Type u) [CommRing R]
variable (f : Z ⟶ Y) [Etale f] (hf : f ≫ p = q)
variable (he : ∀ g, f ≫ (aut τ g).hom = (aut σ g).hom ≫ f)

/-- The actual restriction triangle identifies pulled-back deck coefficients
with the original deck coefficients at the target geometry. -/
def restrictionTriangleIso :
    deckEquivariantFunctor R τ p hp ⋙ equivariantPullback R τ σ f he ≅
      deckEquivariantFunctor R σ q hq :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (trivialEquivariantFunctor X R G)
      (equivariantPullbackComp R 1 τ σ p f
        (deckEquivariantMap τ p hp) he ≪≫
      equivariantPullbackCongr R 1 σ
        (equivariantMap_comp 1 τ σ p f (deckEquivariantMap τ p hp) he)
        (deckEquivariantMap σ q hq) hf)

/-- The equivariant triangle retains ordinary restriction composition and
transport along the supplied over-base equation. -/
@[simp] theorem restrictionTriangleIso_hom_app_hom (M : ModuleSheaf X R) :
    ((restrictionTriangleIso (hp := hp) (hq := hq) R f hf he).hom.app M).hom =
      (restrictionComp p (ModuleCat.{u} R) f).hom.app M ≫
        (restrictionCongr R hf).hom.app M := by
  simp only [restrictionTriangleIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Langlands.Cohomology.TranslationAction.Equivariant.comp_hom,
    equivariantPullbackComp_hom_app_hom, equivariantPullbackCongr_hom_app_hom]
  rfl

/-- The restriction construction gives a coefficient-natural equivariant
section map between the two original deck geometries. -/
def restrictionSectionsMap :
    deckSectionsFunctor R τ p hp ⟶ deckSectionsFunctor R σ q hq :=
  Functor.whiskerLeft (deckEquivariantFunctor R τ p hp)
      (equivariantPullbackSections R τ σ f he) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (restrictionTriangleIso (hp := hp) (hq := hq) R f hf he).hom
      (pullbackSectionsFunctor R σ)

/-- The old section map uses the original geometric pullback followed by
precisely the triangle coefficient map. -/
@[simp] theorem restrictionSectionsMap_app_hom (M : ModuleSheaf X R) :
    ((restrictionSectionsMap (hp := hp) (hq := hq) R f hf he).app M).hom =
      (EtalePullback.sectionsMap f R).app
          ((restriction p (ModuleCat.{u} R)).obj M) ≫
        (EtaleDerivedSections.sections Z R).map
          ((restrictionComp p (ModuleCat.{u} R) f).hom.app M ≫
            (restrictionCongr R hf).hom.app M) := by
  simp only [restrictionSectionsMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp, Action.comp_hom, equivariantPullbackSections_app_hom,
    pullbackSectionsFunctor_map_hom, restrictionTriangleIso_hom_app_hom]
  rfl

/-- The same original restriction triangle gives ordinary cohomology maps. -/
def restrictionCohomologyMap (n : ℕ) :
    deckCohomologyFunctor R τ p hp n ⟶ deckCohomologyFunctor R σ q hq n :=
  Functor.whiskerLeft (deckEquivariantFunctor R τ p hp)
      (equivariantPullbackCohomology R τ σ f he n) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (restrictionTriangleIso (hp := hp) (hq := hq) R f hf he).hom
      (pullbackCohomologyFunctor R σ n)

/-- The ordinary restriction map has the exact original triangle coefficient. -/
@[simp] theorem restrictionCohomologyMap_app_hom (n : ℕ) (M : ModuleSheaf X R) :
    ((restrictionCohomologyMap (hp := hp) (hq := hq) R f hf he n).app M).hom =
      cohomologyMapWithCoefficients f R n
        ((restrictionComp p (ModuleCat.{u} R) f).hom.app M ≫
          (restrictionCongr R hf).hom.app M) := by
  simp only [restrictionCohomologyMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp, Action.comp_hom, equivariantPullbackCohomology_app_hom,
    pullbackCohomologyFunctor_map_hom, restrictionTriangleIso_hom_app_hom]
  rfl

/-- Ordinary degree-zero restriction retains the specified old section
recovery as a full equivariant natural-transformation equality. -/
theorem restrictionCohomologyMap_zero :
    restrictionCohomologyMap (hp := hp) (hq := hq) R f hf he 0 ≫
        (restrictionCohomologyZeroIso σ q hq R).hom =
      (restrictionCohomologyZeroIso τ p hp R).hom ≫
        restrictionSectionsMap (hp := hp) (hq := hq) R f hf he := by
  apply NatTrans.ext
  funext M
  apply Action.Hom.ext
  simp only [NatTrans.comp_app, Action.comp_hom,
    restrictionCohomologyMap_app_hom, restrictionSectionsMap_app_hom,
    restrictionCohomologyZeroIso_hom_app_hom]
  dsimp only [cohomologyMapWithCoefficients]
  rw [Category.assoc, (EtaleDerivedSections.cohomologyZeroIso Z R).hom.naturality,
    ← Category.assoc, EtalePullback.cohomologyMap_zero, Category.assoc]

section Derived

variable [HasDerivedCategory.{wY} (ModuleSheaf Y R)]
variable [HasDerivedCategory.{wY} (ModuleSheaf Z R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Actual derived equivariant restriction followed by the original
restriction triangle, natural in every base coefficient. -/
def restrictionDerivedMap :
    deckDerivedSectionsFunctor R τ p hp ⟶ deckDerivedSectionsFunctor R σ q hq :=
  Functor.whiskerLeft (deckEquivariantFunctor R τ p hp)
      (equivariantPullbackDerivedSections R τ σ f he) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (restrictionTriangleIso (hp := hp) (hq := hq) R f hf he).hom
      (pullbackDerivedSectionsFunctor R σ)

/-- The derived restriction map uses precisely the original geometric map
and the specified restriction triangle coefficient. -/
@[simp] theorem restrictionDerivedMap_app_hom (M : ModuleSheaf X R) :
    ((restrictionDerivedMap (hp := hp) (hq := hq) R f hf he).app M).hom =
      derivedSectionsMapWithCoefficients f R
        ((restrictionComp p (ModuleCat.{u} R) f).hom.app M ≫
          (restrictionCongr R hf).hom.app M) := by
  simp only [restrictionDerivedMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp, Action.comp_hom, equivariantPullbackDerivedSections_app_hom,
    pullbackDerivedSectionsFunctor_map_hom, restrictionTriangleIso_hom_app_hom]
  rfl

/-- The fixed-geometry canonical comparison commutes with the original
geometric derived maps as a full equivariant coefficient-natural square. -/
theorem derivedMap_restriction :
    derivedMap (hp := hp) (hq := hq) f hf he ≫
        (derivedRestrictionIso σ q hq R).hom =
      (derivedRestrictionIso τ p hp R).hom ≫
        restrictionDerivedMap (hp := hp) (hq := hq) R f hf he := by
  apply NatTrans.ext
  funext M
  apply Action.Hom.ext
  simp only [NatTrans.comp_app, Action.comp_hom, derivedMap_app_hom,
    derivedRestrictionIso_hom_app_hom, restrictionDerivedMap_app_hom]
  rw [← EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients_postcomp,
    projectionInverseImageIso_restriction,
    EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients_precomp,
    EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients_restriction]

/-- The restriction-derived map preserves the specified original homology
recovery equivariantly and naturally in every base coefficient. -/
theorem restrictionDerivedMap_homology (n : ℕ) :
    Functor.whiskerRight (restrictionDerivedMap (hp := hp) (hq := hq) R f hf he)
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).mapAction G) ≫
      (deckDerivedHomologyIso R σ q hq n).hom =
    (deckDerivedHomologyIso R τ p hp n).hom ≫
      restrictionCohomologyMap (hp := hp) (hq := hq) R f hf he n := by
  apply NatTrans.ext
  funext M
  apply Action.Hom.ext
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Action.comp_hom,
    Functor.mapAction_map_hom, restrictionDerivedMap_app_hom,
    restrictionCohomologyMap_app_hom]
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).map
      (derivedSectionsMapWithCoefficients f R
        ((restrictionComp p (ModuleCat.{u} R) f).hom.app M ≫
          (restrictionCongr R hf).hom.app M)) ≫
      (𝟙 _ ≫ (EtaleDerivedSectionsPlus.homologyNatIso Z R n).hom.app
        ((restriction q (ModuleCat.{u} R)).obj M)) =
    (𝟙 _ ≫ (EtaleDerivedSectionsPlus.homologyNatIso Y R n).hom.app
        ((restriction p (ModuleCat.{u} R)).obj M)) ≫
      cohomologyMapWithCoefficients f R n
        ((restrictionComp p (ModuleCat.{u} R) f).hom.app M ≫
          (restrictionCongr R hf).hom.app M)
  simpa only [Category.id_comp] using derivedSectionsMapWithCoefficients_homology f R
    ((restrictionComp p (ModuleCat.{u} R) f).hom.app M ≫
      (restrictionCongr R hf).hom.app M) n

/-- The restriction-derived map retains the specified original degree-zero
section recovery as a full equivariant natural-transformation equality. -/
theorem restrictionDerivedMap_zero :
    Functor.whiskerRight (restrictionDerivedMap (hp := hp) (hq := hq) R f hf he)
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≫
      (deckDerivedZeroIso R σ q hq).hom =
    (deckDerivedZeroIso R τ p hp).hom ≫
      restrictionSectionsMap (hp := hp) (hq := hq) R f hf he := by
  apply NatTrans.ext
  funext M
  apply Action.Hom.ext
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Action.comp_hom,
    Functor.mapAction_map_hom, restrictionDerivedMap_app_hom,
    restrictionSectionsMap_app_hom]
  change (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).map
      (derivedSectionsMapWithCoefficients f R
        ((restrictionComp p (ModuleCat.{u} R) f).hom.app M ≫
          (restrictionCongr R hf).hom.app M)) ≫
      (𝟙 _ ≫ ((pullbackDerivedZeroFunctorIso R σ).hom.app
        ((deckEquivariantFunctor R σ q hq).obj M)).hom) =
    (𝟙 _ ≫ ((pullbackDerivedZeroFunctorIso R τ).hom.app
        ((deckEquivariantFunctor R τ p hp).obj M)).hom) ≫ _
  rw [Category.id_comp, Category.id_comp, pullbackDerivedZeroFunctorIso_hom_app_hom,
    pullbackDerivedZeroFunctorIso_hom_app_hom]
  dsimp only [derivedSectionsMapWithCoefficients]
  have hn := (EtaleDerivedSectionsPlus.homologyZeroIso Z R).hom.naturality
    ((restrictionComp p (ModuleCat.{u} R) f).hom.app M ≫
      (restrictionCongr R hf).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [Functor.map_comp, Category.assoc, hn, ← Category.assoc,
    EtalePullback.derivedSectionsMap_zero, Category.assoc]

/-- The canonical ordinary comparison commutes with the same original
geometric map, as an equality of full equivariant natural transformations. -/
theorem cohomologyMap_restriction (n : ℕ) :
    cohomologyMap (hp := hp) (hq := hq) f hf he n ≫
        (cohomologyRestrictionIso σ q hq R n).hom =
      (cohomologyRestrictionIso τ p hp R n).hom ≫
        restrictionCohomologyMap (hp := hp) (hq := hq) R f hf he n := by
  apply (cancel_epi (homologyFunctorIso τ p hp R n).hom).mp
  rw [← Category.assoc, ← derivedMap_homology, Category.assoc,
    ← derivedRestrictionIso_homology, ← Category.assoc,
    ← Functor.whiskerRight_comp, derivedMap_restriction, Functor.whiskerRight_comp,
    Category.assoc, restrictionDerivedMap_homology, ← Category.assoc,
    derivedRestrictionIso_homology, Category.assoc]

/-- The canonical section comparison commutes with the same original
geometric map, retaining both specified degree-zero recovery maps. -/
theorem sectionsMap_restriction :
    sectionsMap (hp := hp) (hq := hq) f hf he ≫
        (sectionsRestrictionIso σ q hq R).hom =
      (sectionsRestrictionIso τ p hp R).hom ≫
        restrictionSectionsMap (hp := hp) (hq := hq) R f hf he := by
  apply (cancel_epi (derivedZeroFunctorIso τ p hp R).hom).mp
  rw [← Category.assoc, ← derivedMap_zero, Category.assoc,
    ← derivedRestrictionIso_zero, ← Category.assoc,
    ← Functor.whiskerRight_comp, derivedMap_restriction, Functor.whiskerRight_comp,
    Category.assoc, restrictionDerivedMap_zero, ← Category.assoc,
    derivedRestrictionIso_zero, Category.assoc]

end Derived

end Langlands.Geometry.EtaleSchemeDeckAction
