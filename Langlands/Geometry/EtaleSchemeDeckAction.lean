import Langlands.Geometry.EtaleCanonicalDeckTower
import Langlands.Geometry.EtaleCohomologyAction
import Mathlib.CategoryTheory.ComposableArrows.Basic

/-! # Canonical deck actions for arbitrary maps of schemes -/

noncomputable section

universe u t wY wR

set_option autoImplicit false

namespace Langlands.Geometry.EtaleSchemeDeckAction

open CategoryTheory AlgebraicGeometry
open EtaleDerivedSections EtaleInverseImage EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X Y Z : Scheme.{u}} {G : Type t} [Group G]
variable (τ : G →* (Aut Y)ᵐᵒᵖ) (p : Y ⟶ X)
variable (hp : ∀ g, (aut τ g).hom ≫ p = p)

/-- Bundle the original deck geometry as an actual action on the opposite
over category. No etaleness of the structure map is required. -/
def overAction : Action ((Over X)ᵒᵖ) G where
  V := Opposite.op (Over.mk p)
  ρ :=
    { toFun := fun g => (Over.homMk (aut τ g).hom (hp g)).op
      map_one' := by
        apply Quiver.Hom.unop_inj
        apply Over.OverMorphism.ext
        exact congrArg Iso.hom (aut_one τ)
      map_mul' := fun g h => by
        apply Quiver.Hom.unop_inj
        apply Over.OverMorphism.ext
        exact congrArg Iso.hom (aut_mul τ g h) }

/-- The source scheme and structure map are the supplied originals. -/
@[simp] theorem overAction_V_left : (overAction τ p hp).V.unop.left = Y := rfl

@[simp] theorem overAction_V_hom : (overAction τ p hp).V.unop.hom = p := rfl

/-- The bundled action retains each original deck automorphism. -/
@[simp] theorem overAction_ρ_left (g : G) :
    ((overAction τ p hp).ρ g).unop.left = (aut τ g).hom := rfl

variable {τ p hp}
variable {σ : G →* (Aut Z)ᵐᵒᵖ} {q : Z ⟶ X}
variable {hq : ∀ g, (aut σ g).hom ≫ q = q}

/-- An arbitrary equivariant map over the base is a morphism of the
constructed contravariant geometric actions. -/
def overHom (f : Z ⟶ Y) (hf : f ≫ p = q)
    (he : ∀ g, f ≫ (aut τ g).hom = (aut σ g).hom ≫ f) :
    overAction τ p hp ⟶ overAction σ q hq where
  hom := (Over.homMk f hf).op
  comm g := by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    exact he g

@[simp] theorem overHom_left (f : Z ⟶ Y) (hf : f ≫ p = q)
    (he : ∀ g, f ≫ (aut τ g).hom = (aut σ g).hom ≫ f) :
    (overHom (hp := hp) (hq := hq) f hf he).hom.unop.left = f := rfl

/-- Identity geometric maps give identity action morphisms. -/
theorem overHom_id :
    overHom (hp := hp) (hq := hp) (𝟙 Y) (by simp)
      (fun _ => by simp) = 𝟙 (overAction τ p hp) := by
  apply Action.Hom.ext
  apply Quiver.Hom.unop_inj
  apply Over.OverMorphism.ext
  rfl

variable {W : Scheme.{u}} {υ : G →* (Aut W)ᵐᵒᵖ} {r : W ⟶ X}
variable {hr : ∀ g, (aut υ g).hom ≫ r = r}

/-- Composition retains the original contravariant scheme-map order. -/
theorem overHom_comp (f : Z ⟶ Y) (hf : f ≫ p = q)
    (he : ∀ g, f ≫ (aut τ g).hom = (aut σ g).hom ≫ f)
    (k : W ⟶ Z) (hk : k ≫ q = r)
    (ke : ∀ g, k ≫ (aut σ g).hom = (aut υ g).hom ≫ k) :
    overHom (hp := hp) (hq := hr) (k ≫ f) (by rw [Category.assoc, hf, hk])
      (fun g => by rw [Category.assoc, he g, ← Category.assoc, ke g, Category.assoc]) =
        overHom (hp := hp) (hq := hq) f hf he ≫
          overHom (hp := hq) (hq := hr) k hk ke := by
  apply Action.Hom.ext
  apply Quiver.Hom.unop_inj
  apply Over.OverMorphism.ext
  rfl

/-- A single original equivariant geometric map gives a two-level tower. -/
def arrowTower (f : Z ⟶ Y) (hf : f ≫ p = q)
    (he : ∀ g, f ≫ (aut τ g).hom = (aut σ g).hom ≫ f) :
    Fin 2 ⥤ Action ((Over X)ᵒᵖ) G :=
  ComposableArrows.mk₁ (overHom (hp := hp) (hq := hq) f hf he)

@[simp] theorem arrowTower_obj_zero (f : Z ⟶ Y) (hf : f ≫ p = q)
    (he : ∀ g, f ≫ (aut τ g).hom = (aut σ g).hom ≫ f) :
    (arrowTower (hp := hp) (hq := hq) f hf he).obj 0 = overAction τ p hp := rfl

@[simp] theorem arrowTower_obj_one (f : Z ⟶ Y) (hf : f ≫ p = q)
    (he : ∀ g, f ≫ (aut τ g).hom = (aut σ g).hom ≫ f) :
    (arrowTower (hp := hp) (hq := hq) f hf he).obj 1 = overAction σ q hq := rfl

variable (τ p hp)

/-- View the original single-scheme action as a constant one-level tower. -/
def tower : SingleObj PUnit.{1} ⥤ Action ((Over X)ᵒᵖ) G :=
  (Functor.const (SingleObj PUnit.{1})).obj (overAction τ p hp)

/-- The coefficient comparison is constructed from composition of inverse
images and the actual geometric deck triangle. -/
def coefficientIso (R : Type u) [CommRing R] (g : G) :
    inverseImage p R ⋙ inverseImage (aut τ g).hom R ≅ inverseImage p R :=
  projectionInverseImageIso R p p (aut τ g).hom (hp g)

variable (R : Type u) [CommRing R]

section Derived

variable [HasDerivedCategory.{wY} (ModuleSheaf Y R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

local instance (x : SingleObj PUnit.{1} × SingleObj G) :
    HasDerivedCategory.{wY}
      (ModuleSheaf ((EtaleCanonicalDeckTower.schemeDiagram (tower τ p hp)).obj x).unop R) :=
  inferInstanceAs (HasDerivedCategory.{wY} (ModuleSheaf Y R))


/-- Canonical global sections with their actual geometric deck action. -/
def sectionsFunctor : ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) G :=
  EtaleCanonicalDeckTower.sectionsFunctor R (tower τ p hp) ⋙
    (evaluation (SingleObj PUnit.{1}) (Action (ModuleCat.{u} R) G)).obj
      (SingleObj.star PUnit.{1})

/-- The original inverse-image coefficient and original scheme are retained. -/
@[simp] theorem sectionsFunctor_obj_V (M : ModuleSheaf X R) :
    ((sectionsFunctor τ p hp R).obj M).V =
      (EtaleDerivedSections.sections Y R).obj ((inverseImage p R).obj M) := rfl

/-- The action uses actual geometric section pullback along the supplied
automorphism, followed by the constructed deck comparison. -/
theorem sectionsFunctor_obj_ρ (M : ModuleSheaf X R) (g : G) :
    ((sectionsFunctor τ p hp R).obj M).ρ g =
      EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients (aut τ g).hom R
        ((coefficientIso τ p hp R g).hom.app M) :=
  EtaleCanonicalDeckTower.sectionsFunctor_obj_obj_ρ R (tower τ p hp) M
    (SingleObj.star PUnit.{1}) g

@[simp] theorem sectionsFunctor_map_hom {M N : ModuleSheaf X R} (α : M ⟶ N) :
    ((sectionsFunctor τ p hp R).map α).hom =
      (EtaleDerivedSections.sections Y R).map ((inverseImage p R).map α) := rfl

/-- Actual bounded-below derived global sections of the original inverse
image, with its deck action, natural in every base coefficient. -/
def derivedFunctor :
    ModuleSheaf X R ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G :=
  EtaleCanonicalDeckTower.derivedFunctor R (tower τ p hp) ⋙
    (evaluation (SingleObj PUnit.{1})
      (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)).obj (SingleObj.star PUnit.{1})

/-- Ordinary cohomology with the same actual geometric deck action. -/
def cohomologyFunctor (n : ℕ) :
    ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) G :=
  EtaleCanonicalDeckTower.cohomologyFunctor R (tower τ p hp) n ⋙
    (evaluation (SingleObj PUnit.{1}) (Action (ModuleCat.{u} R) G)).obj
      (SingleObj.star PUnit.{1})

@[simp] theorem derivedFunctor_obj_V (M : ModuleSheaf X R) :
    ((derivedFunctor τ p hp R).obj M).V =
      (EtaleDerivedSectionsPlus.derivedSections Y R).obj ((inverseImage p R).obj M) := rfl

theorem derivedFunctor_obj_ρ (M : ModuleSheaf X R) (g : G) :
    ((derivedFunctor τ p hp R).obj M).ρ g =
      EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients (aut τ g).hom R
        ((coefficientIso τ p hp R g).hom.app M) :=
  EtaleCanonicalDeckTower.derivedFunctor_obj_obj_ρ R (tower τ p hp) M
    (SingleObj.star PUnit.{1}) g

@[simp] theorem derivedFunctor_map_hom {M N : ModuleSheaf X R} (α : M ⟶ N) :
    ((derivedFunctor τ p hp R).map α).hom =
      (EtaleDerivedSectionsPlus.derivedSections Y R).map
        ((inverseImage p R).map α) := rfl

@[simp] theorem cohomologyFunctor_obj_V (n : ℕ) (M : ModuleSheaf X R) :
    ((cohomologyFunctor τ p hp R n).obj M).V =
      (EtaleDerivedSections.cohomology Y R n).obj ((inverseImage p R).obj M) := rfl

theorem cohomologyFunctor_obj_ρ (n : ℕ) (M : ModuleSheaf X R) (g : G) :
    ((cohomologyFunctor τ p hp R n).obj M).ρ g =
      EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients (aut τ g).hom R n
        ((coefficientIso τ p hp R g).hom.app M) :=
  EtaleCanonicalDeckTower.cohomologyFunctor_obj_obj_ρ R (tower τ p hp) n M
    (SingleObj.star PUnit.{1}) g

@[simp] theorem cohomologyFunctor_map_hom (n : ℕ) {M N : ModuleSheaf X R}
    (α : M ⟶ N) :
    ((cohomologyFunctor τ p hp R n).map α).hom =
      (EtaleDerivedSections.cohomology Y R n).map ((inverseImage p R).map α) := rfl

/-- Homology recovers ordinary cohomology as an isomorphism of the actual
geometric actions, natural in the original base coefficients. -/
def homologyFunctorIso (n : ℕ) :
    derivedFunctor τ p hp R ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).mapAction G ≅
      cohomologyFunctor τ p hp R n :=
  Functor.isoWhiskerRight
    (EtaleCanonicalDeckTower.homologyFunctorIso R (tower τ p hp) n)
    ((evaluation (SingleObj PUnit.{1}) (Action (ModuleCat.{u} R) G)).obj
      (SingleObj.star PUnit.{1}))

/-- Derived degree zero recovers the original global-section action. -/
def derivedZeroFunctorIso :
    derivedFunctor τ p hp R ⋙
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G ≅
      sectionsFunctor τ p hp R :=
  Functor.isoWhiskerRight
    (EtaleCanonicalDeckTower.derivedZeroFunctorIso R (tower τ p hp))
    ((evaluation (SingleObj PUnit.{1}) (Action (ModuleCat.{u} R) G)).obj
      (SingleObj.star PUnit.{1}))

/-- Ordinary degree zero recovers the same global-section action. -/
def cohomologyZeroFunctorIso :
    cohomologyFunctor τ p hp R 0 ≅ sectionsFunctor τ p hp R :=
  Functor.isoWhiskerRight
    (EtaleCanonicalDeckTower.cohomologyZeroFunctorIso R (tower τ p hp))
    ((evaluation (SingleObj PUnit.{1}) (Action (ModuleCat.{u} R) G)).obj
      (SingleObj.star PUnit.{1}))

@[simp] theorem homologyFunctorIso_hom_app_hom (n : ℕ) (M : ModuleSheaf X R) :
    ((homologyFunctorIso τ p hp R n).hom.app M).hom =
      (EtaleDerivedSectionsPlus.homologyNatIso Y R n).hom.app
        ((inverseImage p R).obj M) := rfl

@[simp] theorem derivedZeroFunctorIso_hom_app_hom (M : ModuleSheaf X R) :
    ((derivedZeroFunctorIso τ p hp R).hom.app M).hom =
      (EtaleDerivedSectionsPlus.homologyZeroIso Y R).hom.app
        ((inverseImage p R).obj M) := rfl

@[simp] theorem cohomologyZeroFunctorIso_hom_app_hom (M : ModuleSheaf X R) :
    ((cohomologyZeroFunctorIso τ p hp R).hom.app M).hom =
      (EtaleDerivedSectionsPlus.homologyNatIso Y R 0).inv.app
          ((inverseImage p R).obj M) ≫
        (EtaleDerivedSectionsPlus.homologyZeroIso Y R).hom.app
          ((inverseImage p R).obj M) := rfl

end Derived

section Maps

variable {τ p hp R}
variable (f : Z ⟶ Y) (hf : f ≫ p = q)
variable (he : ∀ g, f ≫ (aut τ g).hom = (aut σ g).hom ≫ f)
variable [HasDerivedCategory.{wY} (ModuleSheaf Y R)]
variable [HasDerivedCategory.{wY} (ModuleSheaf Z R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

@[instance_reducible] private def arrowDerivedCategories (x : Fin 2 × SingleObj G) :
    HasDerivedCategory.{wY}
      (ModuleSheaf ((EtaleCanonicalDeckTower.schemeDiagram
        (arrowTower (hp := hp) (hq := hq) f hf he)).obj x).unop R) :=
by
  rcases x with ⟨i, a⟩
  refine Fin.cases (motive := fun i => HasDerivedCategory.{wY}
    (ModuleSheaf ((EtaleCanonicalDeckTower.schemeDiagram
      (arrowTower (hp := hp) (hq := hq) f hf he)).obj (i, a)).unop R))
    ?_ (fun j => ?_) i
  · exact inferInstanceAs (HasDerivedCategory.{wY} (ModuleSheaf Y R))
  · refine Fin.cases (motive := fun j => HasDerivedCategory.{wY}
      (ModuleSheaf ((EtaleCanonicalDeckTower.schemeDiagram
        (arrowTower (hp := hp) (hq := hq) f hf he)).obj (j.succ, a)).unop R))
      ?_ (fun k => Fin.elim0 k) j
    exact inferInstanceAs (HasDerivedCategory.{wY} (ModuleSheaf Z R))

/-- Arbitrary equivariant scheme maps induce actual derived pullback,
natural in the original base coefficient. -/
def derivedMap :
    derivedFunctor τ p hp R ⟶ derivedFunctor σ q hq R := by
  letI : ∀ x : Fin 2 × SingleObj G, HasDerivedCategory.{wY}
    (ModuleSheaf ((EtaleCanonicalDeckTower.schemeDiagram
      (arrowTower (hp := hp) (hq := hq) f hf he)).obj x).unop R) :=
    arrowDerivedCategories f hf he
  refine { app := fun M => ?_, naturality := ?_ }
  · refine
      { hom := EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients f R
          ((projectionInverseImageIso R p q f hf).hom.app M)
        comm := ?_ }
    intro g
    have h := (((EtaleCanonicalDeckTower.derivedFunctor R
      (arrowTower (hp := hp) (hq := hq) f hf he)).obj M).map
      (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).comm g
    rw [EtaleCanonicalDeckTower.derivedFunctor_obj_obj_ρ,
      EtaleCanonicalDeckTower.derivedFunctor_obj_obj_ρ,
      EtaleCanonicalDeckTower.derivedFunctor_obj_map_hom] at h
    rw [derivedFunctor_obj_ρ, derivedFunctor_obj_ρ]
    exact h
  · intro M N α
    apply Action.Hom.ext
    change (EtaleDerivedSectionsPlus.derivedSections Y R).map
        ((inverseImage p R).map α) ≫
      EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients f R
        ((projectionInverseImageIso R p q f hf).hom.app N) =
      EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients f R
        ((projectionInverseImageIso R p q f hf).hom.app M) ≫
      (EtaleDerivedSectionsPlus.derivedSections Z R).map ((inverseImage q R).map α)
    rw [← EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients_precomp,
      ← EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients_postcomp]
    exact congrArg (EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients f R)
      ((projectionInverseImageIso R p q f hf).hom.naturality α)

/-- Ordinary pullback along the same original geometric map. -/
def cohomologyMap (n : ℕ) :
    cohomologyFunctor τ p hp R n ⟶ cohomologyFunctor σ q hq R n := by
  letI : ∀ x : Fin 2 × SingleObj G, HasDerivedCategory.{wY}
    (ModuleSheaf ((EtaleCanonicalDeckTower.schemeDiagram
      (arrowTower (hp := hp) (hq := hq) f hf he)).obj x).unop R) :=
    arrowDerivedCategories f hf he
  refine { app := fun M => ?_, naturality := ?_ }
  · refine
      { hom := EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients f R n
          ((projectionInverseImageIso R p q f hf).hom.app M)
        comm := ?_ }
    intro g
    have h := (((EtaleCanonicalDeckTower.cohomologyFunctor R
      (arrowTower (hp := hp) (hq := hq) f hf he) n).obj M).map
      (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).comm g
    rw [EtaleCanonicalDeckTower.cohomologyFunctor_obj_obj_ρ,
      EtaleCanonicalDeckTower.cohomologyFunctor_obj_obj_ρ,
      EtaleCanonicalDeckTower.cohomologyFunctor_obj_map_hom] at h
    rw [cohomologyFunctor_obj_ρ, cohomologyFunctor_obj_ρ]
    exact h
  · intro M N α
    apply Action.Hom.ext
    change (EtaleDerivedSections.cohomology Y R n).map ((inverseImage p R).map α) ≫
        EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients f R n
          ((projectionInverseImageIso R p q f hf).hom.app N) =
      EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients f R n
          ((projectionInverseImageIso R p q f hf).hom.app M) ≫
        (EtaleDerivedSections.cohomology Z R n).map ((inverseImage q R).map α)
    let η := Functor.whiskerLeft (inverseImage p R)
        (EtaleDerivedGlobalPullback.cohomologyPullback f R n) ≫
      (Functor.associator (inverseImage p R) (inverseImage f R)
        (EtaleDerivedSections.cohomology Z R n)).inv ≫
      Functor.whiskerRight (projectionInverseImageIso R p q f hf).hom
        (EtaleDerivedSections.cohomology Z R n)
    simpa only [η, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app,
      Functor.comp_map, Category.id_comp, Category.comp_id,
      Category.assoc, EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients]
      using η.naturality α

/-- Global-section pullback along the same original geometric map. -/
def sectionsMap :
    sectionsFunctor τ p hp R ⟶ sectionsFunctor σ q hq R := by
  letI : ∀ x : Fin 2 × SingleObj G, HasDerivedCategory.{wY}
    (ModuleSheaf ((EtaleCanonicalDeckTower.schemeDiagram
      (arrowTower (hp := hp) (hq := hq) f hf he)).obj x).unop R) :=
    arrowDerivedCategories f hf he
  refine { app := fun M => ?_, naturality := ?_ }
  · refine
      { hom := EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients f R
          ((projectionInverseImageIso R p q f hf).hom.app M)
        comm := ?_ }
    intro g
    have h := (((EtaleCanonicalDeckTower.sectionsFunctor R
      (arrowTower (hp := hp) (hq := hq) f hf he)).obj M).map
      (homOfLE (show (0 : Fin 2) ≤ 1 by decide))).comm g
    rw [EtaleCanonicalDeckTower.sectionsFunctor_obj_obj_ρ,
      EtaleCanonicalDeckTower.sectionsFunctor_obj_obj_ρ,
      EtaleCanonicalDeckTower.sectionsFunctor_obj_map_hom] at h
    rw [sectionsFunctor_obj_ρ, sectionsFunctor_obj_ρ]
    exact h
  · intro M N α
    apply Action.Hom.ext
    change (EtaleDerivedSections.sections Y R).map ((inverseImage p R).map α) ≫
        EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients f R
          ((projectionInverseImageIso R p q f hf).hom.app N) =
      EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients f R
          ((projectionInverseImageIso R p q f hf).hom.app M) ≫
        (EtaleDerivedSections.sections Z R).map ((inverseImage q R).map α)
    let η := Functor.whiskerLeft (inverseImage p R)
        (EtaleDerivedGlobalPullback.sectionsPullback f R) ≫
      (Functor.associator (inverseImage p R) (inverseImage f R)
        (EtaleDerivedSections.sections Z R)).inv ≫
      Functor.whiskerRight (projectionInverseImageIso R p q f hf).hom
        (EtaleDerivedSections.sections Z R)
    simpa only [η, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_inv_app,
      Functor.comp_map, Category.id_comp, Category.comp_id,
      Category.assoc, EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients]
      using η.naturality α

/-- The derived natural transformation is exactly original-map pullback. -/
@[simp] theorem derivedMap_app_hom (M : ModuleSheaf X R) :
    ((derivedMap (hp := hp) (hq := hq) f hf he).app M).hom =
      EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients f R
        ((projectionInverseImageIso R p q f hf).hom.app M) := rfl

/-- The same formula holds in each ordinary cohomology degree. -/
@[simp] theorem cohomologyMap_app_hom (n : ℕ) (M : ModuleSheaf X R) :
    ((cohomologyMap (hp := hp) (hq := hq) f hf he n).app M).hom =
      EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients f R n
        ((projectionInverseImageIso R p q f hf).hom.app M) := rfl

/-- The section natural transformation retains the actual geometric map. -/
@[simp] theorem sectionsMap_app_hom (M : ModuleSheaf X R) :
    ((sectionsMap (hp := hp) (hq := hq) f hf he).app M).hom =
      EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients f R
        ((projectionInverseImageIso R p q f hf).hom.app M) := rfl

/-- Original-map pullback preserves the specified homology recovery as an
 equality of equivariant natural transformations in all base coefficients. -/
theorem derivedMap_homology (n : ℕ) :
    Functor.whiskerRight (derivedMap (hp := hp) (hq := hq) f hf he)
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).mapAction G) ≫
      (homologyFunctorIso σ q hq R n).hom =
    (homologyFunctorIso τ p hp R n).hom ≫ cohomologyMap (hp := hp) (hq := hq) f hf he n := by
  apply NatTrans.ext
  funext M
  apply Action.Hom.ext
  exact EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients_homology
    f R n ((projectionInverseImageIso R p q f hf).hom.app M)

/-- Original-map pullback also preserves the specified derived degree-zero
 recovery of the global-section action. -/
theorem derivedMap_zero :
    Functor.whiskerRight (derivedMap (hp := hp) (hq := hq) f hf he)
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≫
      (derivedZeroFunctorIso σ q hq R).hom =
    (derivedZeroFunctorIso τ p hp R).hom ≫ sectionsMap (hp := hp) (hq := hq) f hf he := by
  apply NatTrans.ext
  funext M
  apply Action.Hom.ext
  exact EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients_zero
    f R ((projectionInverseImageIso R p q f hf).hom.app M)

/-- Ordinary degree-zero recovery commutes with the same original-map
 pullback, with the parent's specified comparison. -/
theorem cohomologyMap_zero :
    cohomologyMap (hp := hp) (hq := hq) f hf he 0 ≫ (cohomologyZeroFunctorIso σ q hq R).hom =
      (cohomologyZeroFunctorIso τ p hp R).hom ≫ sectionsMap (hp := hp) (hq := hq) f hf he := by
  let : ∀ x : Fin 2 × SingleObj G, HasDerivedCategory.{wY}
    (ModuleSheaf ((EtaleCanonicalDeckTower.schemeDiagram
      (arrowTower (hp := hp) (hq := hq) f hf he)).obj x).unop R) :=
    arrowDerivedCategories f hf he
  apply NatTrans.ext
  funext M
  apply Action.Hom.ext
  have h := ((EtaleCanonicalDeckTower.cohomologyZeroFunctorIso R
    (arrowTower (hp := hp) (hq := hq) f hf he)).hom.app M).naturality
    (homOfLE (show (0 : Fin 2) ≤ 1 by decide))
  have h' := congrArg Action.Hom.hom h
  simp only [Action.comp_hom,
    EtaleCanonicalDeckTower.cohomologyFunctor_obj_map_hom,
    EtaleCanonicalDeckTower.sectionsFunctor_obj_map_hom,
    EtaleCanonicalDeckTower.cohomologyZeroFunctorIso_hom_app_app_hom] at h'
  exact h'

end Maps

end Langlands.Geometry.EtaleSchemeDeckAction
