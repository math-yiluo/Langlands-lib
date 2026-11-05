import Langlands.Geometry.EtaleSchemeDeckAction

/-! # Raw scheme deck geometry and its cohomological functors -/

noncomputable section

universe u t wY wR

set_option autoImplicit false

namespace Langlands.Geometry.EtaleSchemeDeckAction

open CategoryTheory AlgebraicGeometry
open EtaleDerivedSections EtaleInverseImage EtaleCohomologyAction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Original scheme geometry with an actual deck action over a fixed base. -/
structure Datum (X : Scheme.{u}) (G : Type t) [Group G] where
  space : Scheme.{u}
  projection : space ⟶ X
  action : G →* (Aut space)ᵐᵒᵖ
  over_base : ∀ g, (aut action g).hom ≫ projection = projection

namespace Datum

variable {X : Scheme.{u}} {G : Type t} [Group G]

/-- Arrows follow cohomological variance: an arrow from A to B is an actual
 equivariant scheme map from B to A over the base. -/
@[ext] structure Hom (A B : Datum X G) where
  map : B.space ⟶ A.space
  over_base : map ≫ A.projection = B.projection
  equivariant : ∀ g, map ≫ (aut A.action g).hom = (aut B.action g).hom ≫ map

instance : Category (Datum X G) where
  Hom := Hom
  id A := ⟨𝟙 A.space, by simp, fun _ => by simp⟩
  comp f k := ⟨k.map ≫ f.map,
    by rw [Category.assoc, f.over_base, k.over_base],
    fun g => by rw [Category.assoc, f.equivariant g, ← Category.assoc,
      k.equivariant g, Category.assoc]⟩
  id_comp f := by apply Hom.ext; simp
  comp_id f := by apply Hom.ext; simp
  assoc f k l := by apply Hom.ext; exact (Category.assoc _ _ _).symm

@[simp] theorem id_map (A : Datum X G) : (𝟙 A : A ⟶ A).map = 𝟙 A.space := rfl

@[simp] theorem comp_map {A B C : Datum X G} (f : A ⟶ B) (k : B ⟶ C) :
    (f ≫ k).map = k.map ≫ f.map := rfl

/-- Forget only the raw presentation, retaining the actual opposite over action. -/
def overActionFunctor : Datum X G ⥤ Action ((Over X)ᵒᵖ) G where
  obj A := overAction A.action A.projection A.over_base
  map f := overHom f.map f.over_base f.equivariant
  map_id _ := overHom_id
  map_comp f k := overHom_comp f.map f.over_base f.equivariant
    k.map k.over_base k.equivariant

@[simp] theorem overActionFunctor_map_left {A B : Datum X G} (f : A ⟶ B) :
    ((overActionFunctor.map f).hom.unop.left) = f.map := rfl

instance : (overActionFunctor (X := X) (G := G)).Faithful where
  map_injective h := by
    apply Hom.ext
    exact congrArg (fun a => a.hom.unop.left) h

end Datum

section MapLaws

variable {X Y Z W : Scheme.{u}} {G : Type t} [Group G]
variable {τ : G →* (Aut Y)ᵐᵒᵖ} {σ : G →* (Aut Z)ᵐᵒᵖ}
variable {υ : G →* (Aut W)ᵐᵒᵖ}
variable {p : Y ⟶ X} {q : Z ⟶ X} {r : W ⟶ X}
variable {hp : ∀ g, (aut τ g).hom ≫ p = p}
variable {hq : ∀ g, (aut σ g).hom ≫ q = q}
variable {hr : ∀ g, (aut υ g).hom ≫ r = r}
variable {R : Type u} [CommRing R]
variable [HasDerivedCategory.{wY} (ModuleSheaf Y R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- The original identity triangle induces identity derived pullback. -/
@[simp] theorem derivedMap_id :
    derivedMap (hp := hp) (hq := hp) (R := R) (𝟙 Y) (by simp)
      (fun _ => by simp) = 𝟙 (derivedFunctor τ p hp R) := by
  apply NatTrans.ext
  funext M
  apply Action.Hom.ext
  rw [derivedMap_app_hom, projectionInverseImageIso_id R p (𝟙 Y) (by simp) rfl M]
  simp

/-- Ordinary cohomology retains the original identity map. -/
@[simp] theorem cohomologyMap_id (n : ℕ) :
    cohomologyMap (hp := hp) (hq := hp) (R := R) (𝟙 Y) (by simp)
      (fun _ => by simp) n = 𝟙 (cohomologyFunctor τ p hp R n) := by
  apply (cancel_epi (homologyFunctorIso τ p hp R n).hom).mp
  have h := derivedMap_homology (hp := hp) (hq := hp) (R := R)
    (𝟙 Y) (by simp) (fun _ => by simp) n
  simpa only [derivedMap_id, Functor.whiskerRight_id', Category.id_comp,
    Category.comp_id] using h.symm

/-- Sections retain the original identity map. -/
@[simp] theorem sectionsMap_id :
    sectionsMap (hp := hp) (hq := hp) (R := R) (𝟙 Y) (by simp)
      (fun _ => by simp) = 𝟙 (sectionsFunctor τ p hp R) := by
  apply (cancel_epi (derivedZeroFunctorIso τ p hp R).hom).mp
  have h := derivedMap_zero (hp := hp) (hq := hp) (R := R)
    (𝟙 Y) (by simp) (fun _ => by simp)
  simpa only [derivedMap_id, Functor.whiskerRight_id', Category.id_comp,
    Category.comp_id] using h.symm

variable [HasDerivedCategory.{wY} (ModuleSheaf Z R)]
variable [HasDerivedCategory.{wY} (ModuleSheaf W R)]

/-- Successive original equivariant maps compose with precisely the canonical
 coefficient comparison for their original scheme-map composite. -/
theorem derivedMap_comp (f : Z ⟶ Y) (hf : f ≫ p = q)
    (he : ∀ g, f ≫ (aut τ g).hom = (aut σ g).hom ≫ f)
    (k : W ⟶ Z) (hk : k ≫ q = r)
    (ke : ∀ g, k ≫ (aut σ g).hom = (aut υ g).hom ≫ k) :
    derivedMap (hp := hp) (hq := hq) (R := R) f hf he ≫
      derivedMap (hp := hq) (hq := hr) k hk ke =
    derivedMap (hp := hp) (hq := hr) (k ≫ f) (by rw [Category.assoc, hf, hk])
      (fun g => by rw [Category.assoc, he g, ← Category.assoc, ke g, Category.assoc]) := by
  apply NatTrans.ext
  funext M
  apply Action.Hom.ext
  simp only [NatTrans.comp_app, Action.comp_hom, derivedMap_app_hom]
  rw [EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients_comp]
  congr 1
  rw [projectionInverseImageIso_comp R p q r f k (k ≫ f) hf hk
    (by rw [Category.assoc, hf, hk]) rfl M]
  simp only [inverseImageCongr_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Iso.inv_hom_id_app_assoc]

/-- Ordinary cohomology preserves successive original geometric maps. -/
theorem cohomologyMap_comp (f : Z ⟶ Y) (hf : f ≫ p = q)
    (he : ∀ g, f ≫ (aut τ g).hom = (aut σ g).hom ≫ f)
    (k : W ⟶ Z) (hk : k ≫ q = r)
    (ke : ∀ g, k ≫ (aut σ g).hom = (aut υ g).hom ≫ k) (n : ℕ) :
    cohomologyMap (hp := hp) (hq := hq) (R := R) f hf he n ≫
      cohomologyMap (hp := hq) (hq := hr) k hk ke n =
    cohomologyMap (hp := hp) (hq := hr) (k ≫ f) (by rw [Category.assoc, hf, hk])
      (fun g => by rw [Category.assoc, he g, ← Category.assoc, ke g, Category.assoc]) n := by
  apply (cancel_epi (homologyFunctorIso τ p hp R n).hom).mp
  rw [← Category.assoc, ← derivedMap_homology f hf he n, Category.assoc,
    ← derivedMap_homology k hk ke n, ← Category.assoc,
    ← Functor.whiskerRight_comp, derivedMap_comp, derivedMap_homology]

/-- Sections preserve the same successive original geometric maps. -/
theorem sectionsMap_comp (f : Z ⟶ Y) (hf : f ≫ p = q)
    (he : ∀ g, f ≫ (aut τ g).hom = (aut σ g).hom ≫ f)
    (k : W ⟶ Z) (hk : k ≫ q = r)
    (ke : ∀ g, k ≫ (aut σ g).hom = (aut υ g).hom ≫ k) :
    sectionsMap (hp := hp) (hq := hq) (R := R) f hf he ≫
      sectionsMap (hp := hq) (hq := hr) k hk ke =
    sectionsMap (hp := hp) (hq := hr) (k ≫ f) (by rw [Category.assoc, hf, hk])
      (fun g => by rw [Category.assoc, he g, ← Category.assoc, ke g, Category.assoc]) := by
  apply (cancel_epi (derivedZeroFunctorIso τ p hp R).hom).mp
  rw [← Category.assoc, ← derivedMap_zero f hf he, Category.assoc,
    ← derivedMap_zero k hk ke, ← Category.assoc,
    ← Functor.whiskerRight_comp, derivedMap_comp, derivedMap_zero]

end MapLaws

namespace Datum

variable {X : Scheme.{u}} {G : Type t} [Group G]
variable (R : Type u) [CommRing R]
variable [∀ A : Datum X G, HasDerivedCategory.{wY} (ModuleSheaf A.space R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Derived sections form a functor in actual raw geometry with values in
 functors on all original base coefficients. -/
def derivedConsumer :
    Datum X G ⥤ (ModuleSheaf X R ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G) where
  obj A := derivedFunctor A.action A.projection A.over_base R
  map f := derivedMap f.map f.over_base f.equivariant
  map_id _ := derivedMap_id
  map_comp f k := (derivedMap_comp f.map f.over_base f.equivariant
    k.map k.over_base k.equivariant).symm

/-- Ordinary cohomology is functorial in the same geometry and all base sheaves. -/
def cohomologyConsumer (n : ℕ) :
    Datum X G ⥤ (ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) G) where
  obj A := cohomologyFunctor A.action A.projection A.over_base R n
  map f := cohomologyMap f.map f.over_base f.equivariant n
  map_id _ := cohomologyMap_id n
  map_comp f k := (cohomologyMap_comp f.map f.over_base f.equivariant
    k.map k.over_base k.equivariant n).symm

/-- Global sections are functorial in the same geometry and all base sheaves. -/
def sectionsConsumer : Datum X G ⥤ (ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) G) where
  obj A := sectionsFunctor A.action A.projection A.over_base R
  map f := sectionsMap f.map f.over_base f.equivariant
  map_id _ := sectionsMap_id
  map_comp f k := (sectionsMap_comp f.map f.over_base f.equivariant
    k.map k.over_base k.equivariant).symm

/-- Evaluation retains the original scheme and inverse-image coefficient. -/
@[simp] theorem derivedConsumer_obj_obj_V (A : Datum X G) (M : ModuleSheaf X R) :
    (((derivedConsumer R).obj A).obj M).V =
      (EtaleDerivedSectionsPlus.derivedSections A.space R).obj
        ((inverseImage A.projection R).obj M) := rfl

@[simp] theorem cohomologyConsumer_obj_obj_V (n : ℕ) (A : Datum X G)
    (M : ModuleSheaf X R) :
    (((cohomologyConsumer R n).obj A).obj M).V =
      (EtaleDerivedSections.cohomology A.space R n).obj
        ((inverseImage A.projection R).obj M) := rfl

@[simp] theorem sectionsConsumer_obj_obj_V (A : Datum X G) (M : ModuleSheaf X R) :
    (((sectionsConsumer R).obj A).obj M).V =
      (EtaleDerivedSections.sections A.space R).obj
        ((inverseImage A.projection R).obj M) := rfl

/-- Each action is pullback along the original automorphism with its canonical
 inverse-image coefficient, rather than an independently chosen action. -/
theorem derivedConsumer_obj_obj_ρ (A : Datum X G) (M : ModuleSheaf X R) (g : G) :
    (((derivedConsumer R).obj A).obj M).ρ g =
      EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients (aut A.action g).hom R
        ((coefficientIso A.action A.projection A.over_base R g).hom.app M) :=
  derivedFunctor_obj_ρ A.action A.projection A.over_base R M g

theorem cohomologyConsumer_obj_obj_ρ (n : ℕ) (A : Datum X G)
    (M : ModuleSheaf X R) (g : G) :
    (((cohomologyConsumer R n).obj A).obj M).ρ g =
      EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients (aut A.action g).hom R n
        ((coefficientIso A.action A.projection A.over_base R g).hom.app M) :=
  cohomologyFunctor_obj_ρ A.action A.projection A.over_base R n M g

theorem sectionsConsumer_obj_obj_ρ (A : Datum X G) (M : ModuleSheaf X R) (g : G) :
    (((sectionsConsumer R).obj A).obj M).ρ g =
      EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients (aut A.action g).hom R
        ((coefficientIso A.action A.projection A.over_base R g).hom.app M) :=
  sectionsFunctor_obj_ρ A.action A.projection A.over_base R M g

/-- Base coefficient maps retain the actual inverse-image morphism. -/
@[simp] theorem derivedConsumer_obj_map_hom (A : Datum X G)
    {M N : ModuleSheaf X R} (α : M ⟶ N) :
    (((derivedConsumer R).obj A).map α).hom =
      (EtaleDerivedSectionsPlus.derivedSections A.space R).map
        ((inverseImage A.projection R).map α) := rfl

@[simp] theorem cohomologyConsumer_obj_map_hom (n : ℕ) (A : Datum X G)
    {M N : ModuleSheaf X R} (α : M ⟶ N) :
    (((cohomologyConsumer R n).obj A).map α).hom =
      (EtaleDerivedSections.cohomology A.space R n).map
        ((inverseImage A.projection R).map α) := rfl

@[simp] theorem sectionsConsumer_obj_map_hom (A : Datum X G)
    {M N : ModuleSheaf X R} (α : M ⟶ N) :
    (((sectionsConsumer R).obj A).map α).hom =
      (EtaleDerivedSections.sections A.space R).map
        ((inverseImage A.projection R).map α) := rfl

/-- Geometric arrows retain original-map derived pullback with its canonical
 inverse-image triangle coefficient, naturally in every base sheaf. -/
@[simp] theorem derivedConsumer_map_app_hom {A B : Datum X G} (f : A ⟶ B)
    (M : ModuleSheaf X R) :
    (((derivedConsumer R).map f).app M).hom =
      EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients f.map R
        ((projectionInverseImageIso R A.projection B.projection f.map f.over_base).hom.app M) := rfl

@[simp] theorem cohomologyConsumer_map_app_hom (n : ℕ) {A B : Datum X G}
    (f : A ⟶ B) (M : ModuleSheaf X R) :
    (((cohomologyConsumer R n).map f).app M).hom =
      EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients f.map R n
        ((projectionInverseImageIso R A.projection B.projection f.map f.over_base).hom.app M) := rfl

@[simp] theorem sectionsConsumer_map_app_hom {A B : Datum X G} (f : A ⟶ B)
    (M : ModuleSheaf X R) :
    (((sectionsConsumer R).map f).app M).hom =
      EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients f.map R
        ((projectionInverseImageIso R A.projection B.projection f.map f.over_base).hom.app M) := rfl

/-- The specified homology recovery is natural in geometric arrows as well
 as in all coefficients, with the full original group action. -/
def homologyConsumerIso (n : ℕ) :
    derivedConsumer (X := X) (G := G) R ⋙
        (Functor.whiskeringRight (ModuleSheaf X R)
          (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).mapAction G) ≅
      cohomologyConsumer R n :=
  NatIso.ofComponents (fun A => homologyFunctorIso A.action A.projection A.over_base R n)
    (fun f => derivedMap_homology f.map f.over_base f.equivariant n)

/-- The specified derived degree-zero recovery is natural in both inputs. -/
def derivedZeroConsumerIso :
    derivedConsumer (X := X) (G := G) R ⋙
        (Functor.whiskeringRight (ModuleSheaf X R)
          (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≅
      sectionsConsumer R :=
  NatIso.ofComponents (fun A => derivedZeroFunctorIso A.action A.projection A.over_base R)
    (fun f => derivedMap_zero f.map f.over_base f.equivariant)

/-- The specified ordinary degree-zero recovery is natural in both inputs. -/
def cohomologyZeroConsumerIso :
    cohomologyConsumer (X := X) (G := G) R 0 ≅ sectionsConsumer R :=
  NatIso.ofComponents (fun A => cohomologyZeroFunctorIso A.action A.projection A.over_base R)
    (fun f => cohomologyMap_zero f.map f.over_base f.equivariant)

/-- The two-input comparison retains the specified original-scheme homology
 recovery, component by component. -/
@[simp] theorem homologyConsumerIso_hom_app_app_hom (n : ℕ) (A : Datum X G)
    (M : ModuleSheaf X R) :
    (((homologyConsumerIso R n).hom.app A).app M).hom =
      (EtaleDerivedSectionsPlus.homologyNatIso A.space R n).hom.app
        ((inverseImage A.projection R).obj M) := rfl

@[simp] theorem derivedZeroConsumerIso_hom_app_app_hom (A : Datum X G)
    (M : ModuleSheaf X R) :
    (((derivedZeroConsumerIso R).hom.app A).app M).hom =
      (EtaleDerivedSectionsPlus.homologyZeroIso A.space R).hom.app
        ((inverseImage A.projection R).obj M) := rfl

@[simp] theorem cohomologyZeroConsumerIso_hom_app_app_hom (A : Datum X G)
    (M : ModuleSheaf X R) :
    (((cohomologyZeroConsumerIso R).hom.app A).app M).hom =
      (EtaleDerivedSectionsPlus.homologyNatIso A.space R 0).inv.app
          ((inverseImage A.projection R).obj M) ≫
        (EtaleDerivedSectionsPlus.homologyZeroIso A.space R).hom.app
          ((inverseImage A.projection R).obj M) := rfl

end Datum

end Langlands.Geometry.EtaleSchemeDeckAction
