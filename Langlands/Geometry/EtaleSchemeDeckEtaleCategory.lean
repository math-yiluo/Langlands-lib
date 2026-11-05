import Langlands.Geometry.EtaleSchemeDeckCategory
import Langlands.Geometry.EtaleSchemeDeckMapRestriction

/-! # Etale deck geometry and natural restriction comparisons -/

noncomputable section

universe u t wY wR

set_option autoImplicit false

namespace Langlands.Geometry.EtaleSchemeDeckAction

open CategoryTheory AlgebraicGeometry
open EtaleDerivedSections EtaleInverseImage EtaleCohomologyAction EtalePullback

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- An original deck geometry with an etale projection to the fixed base. -/
structure EtaleDatum (X : Scheme.{u}) (G : Type t) [Group G] extends Datum X G where
  etale_projection : Etale projection

namespace EtaleDatum

variable {X : Scheme.{u}} {G : Type t} [Group G]

instance (A : EtaleDatum X G) : Etale A.projection := A.etale_projection

/-- An original equivariant map in cohomological variance, required to be etale. -/
@[ext] structure Hom (A B : EtaleDatum X G) extends Datum.Hom A.toDatum B.toDatum where
  etale_map : Etale map

instance {A B : EtaleDatum X G} (f : Hom A B) : Etale f.map := f.etale_map

instance : Category (EtaleDatum X G) where
  Hom := Hom
  id A :=
    { map := 𝟙 A.space
      over_base := by simp
      equivariant := fun _ => by simp
      etale_map := inferInstance }
  comp f k :=
    { map := k.map ≫ f.map
      over_base := by rw [Category.assoc, f.over_base, k.over_base]
      equivariant := fun g => by
        rw [Category.assoc, f.equivariant g, ← Category.assoc,
          k.equivariant g, Category.assoc]
      etale_map := inferInstance }
  id_comp f := by apply Hom.ext; simp
  comp_id f := by apply Hom.ext; simp
  assoc f k l := by apply Hom.ext; exact (Category.assoc _ _ _).symm

@[simp] theorem id_map (A : EtaleDatum X G) : (𝟙 A : A ⟶ A).map = 𝟙 A.space := rfl

@[simp] theorem comp_map {A B C : EtaleDatum X G} (f : A ⟶ B) (k : B ⟶ C) :
    (f ≫ k).map = k.map ≫ f.map := rfl

/-- Forget only etaleness, preserving the original geometry and arrow. -/
def forget : EtaleDatum X G ⥤ Datum X G where
  obj A := A.toDatum
  map f := f.toHom
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem forget_map_map {A B : EtaleDatum X G} (f : A ⟶ B) :
    (forget.map f).map = f.map := rfl

instance : (forget (X := X) (G := G)).Faithful where
  map_injective h := Hom.ext (congrArg Datum.Hom.map h)

variable (R : Type u) [CommRing R]
variable [∀ A : Datum X G, HasDerivedCategory.{wY} (ModuleSheaf A.space R)]
variable [HasDerivedCategory.{wR} (ModuleCat.{u} R)]

/-- Canonical inverse-image derived consumers, reused along faithful forgetting. -/
def derivedConsumer :
    EtaleDatum X G ⥤ (ModuleSheaf X R ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G) :=
  forget ⋙ Datum.derivedConsumer R

/-- Canonical ordinary cohomology consumers on original etale geometry. -/
def cohomologyConsumer (n : ℕ) :
    EtaleDatum X G ⥤ (ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) G) :=
  forget ⋙ Datum.cohomologyConsumer R n

/-- Canonical section consumers on original etale geometry. -/
def sectionsConsumer :
    EtaleDatum X G ⥤ (ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) G) :=
  forget ⋙ Datum.sectionsConsumer R

/-- Evaluation retains the original scheme and inverse-image coefficient. -/
@[simp] theorem derivedConsumer_obj_obj_V (A : EtaleDatum X G) (M : ModuleSheaf X R) :
    (((derivedConsumer R).obj A).obj M).V =
      (EtaleDerivedSectionsPlus.derivedSections A.space R).obj
        ((inverseImage A.projection R).obj M) := rfl

@[simp] theorem cohomologyConsumer_obj_obj_V (n : ℕ) (A : EtaleDatum X G)
    (M : ModuleSheaf X R) :
    (((cohomologyConsumer R n).obj A).obj M).V =
      (EtaleDerivedSections.cohomology A.space R n).obj
        ((inverseImage A.projection R).obj M) := rfl

@[simp] theorem sectionsConsumer_obj_obj_V (A : EtaleDatum X G) (M : ModuleSheaf X R) :
    (((sectionsConsumer R).obj A).obj M).V =
      (EtaleDerivedSections.sections A.space R).obj
        ((inverseImage A.projection R).obj M) := rfl

/-- Each action is pullback along the original automorphism with its canonical
 inverse-image coefficient, rather than an independently chosen action. -/
theorem derivedConsumer_obj_obj_ρ (A : EtaleDatum X G) (M : ModuleSheaf X R) (g : G) :
    (((derivedConsumer R).obj A).obj M).ρ g =
      EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients (aut A.action g).hom R
        ((coefficientIso A.action A.projection A.over_base R g).hom.app M) :=
  derivedFunctor_obj_ρ A.action A.projection A.over_base R M g

theorem cohomologyConsumer_obj_obj_ρ (n : ℕ) (A : EtaleDatum X G)
    (M : ModuleSheaf X R) (g : G) :
    (((cohomologyConsumer R n).obj A).obj M).ρ g =
      EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients (aut A.action g).hom R n
        ((coefficientIso A.action A.projection A.over_base R g).hom.app M) :=
  cohomologyFunctor_obj_ρ A.action A.projection A.over_base R n M g

theorem sectionsConsumer_obj_obj_ρ (A : EtaleDatum X G) (M : ModuleSheaf X R) (g : G) :
    (((sectionsConsumer R).obj A).obj M).ρ g =
      EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients (aut A.action g).hom R
        ((coefficientIso A.action A.projection A.over_base R g).hom.app M) :=
  sectionsFunctor_obj_ρ A.action A.projection A.over_base R M g

/-- Base coefficient maps retain the actual inverse-image morphism. -/
@[simp] theorem derivedConsumer_obj_map_hom (A : EtaleDatum X G)
    {M N : ModuleSheaf X R} (α : M ⟶ N) :
    (((derivedConsumer R).obj A).map α).hom =
      (EtaleDerivedSectionsPlus.derivedSections A.space R).map
        ((inverseImage A.projection R).map α) := rfl

@[simp] theorem cohomologyConsumer_obj_map_hom (n : ℕ) (A : EtaleDatum X G)
    {M N : ModuleSheaf X R} (α : M ⟶ N) :
    (((cohomologyConsumer R n).obj A).map α).hom =
      (EtaleDerivedSections.cohomology A.space R n).map
        ((inverseImage A.projection R).map α) := rfl

@[simp] theorem sectionsConsumer_obj_map_hom (A : EtaleDatum X G)
    {M N : ModuleSheaf X R} (α : M ⟶ N) :
    (((sectionsConsumer R).obj A).map α).hom =
      (EtaleDerivedSections.sections A.space R).map
        ((inverseImage A.projection R).map α) := rfl

/-- Geometric arrows retain original-map derived pullback with its canonical
 inverse-image triangle coefficient, naturally in every base sheaf. -/
@[simp] theorem derivedConsumer_map_app_hom {A B : EtaleDatum X G} (f : A ⟶ B)
    (M : ModuleSheaf X R) :
    (((derivedConsumer R).map f).app M).hom =
      EtaleDerivedGlobalPullback.sheafDerivedPullbackWithCoefficients f.map R
        ((projectionInverseImageIso R A.projection B.projection f.map f.over_base).hom.app M) := rfl

@[simp] theorem cohomologyConsumer_map_app_hom (n : ℕ) {A B : EtaleDatum X G}
    (f : A ⟶ B) (M : ModuleSheaf X R) :
    (((cohomologyConsumer R n).map f).app M).hom =
      EtaleDerivedGlobalPullback.cohomologyPullbackWithCoefficients f.map R n
        ((projectionInverseImageIso R A.projection B.projection f.map f.over_base).hom.app M) := rfl

@[simp] theorem sectionsConsumer_map_app_hom {A B : EtaleDatum X G} (f : A ⟶ B)
    (M : ModuleSheaf X R) :
    (((sectionsConsumer R).map f).app M).hom =
      EtaleDerivedGlobalPullback.sectionsPullbackWithCoefficients f.map R
        ((projectionInverseImageIso R A.projection B.projection f.map f.over_base).hom.app M) := rfl

/-- Actual restriction-derived objects and original restriction maps form a functor. -/
def restrictionDerivedConsumer :
    EtaleDatum X G ⥤ (ModuleSheaf X R ⥤ Action (DerivedCategory.Plus (ModuleCat.{u} R)) G) where
  obj A := deckDerivedSectionsFunctor R A.action A.projection A.over_base
  map f := restrictionDerivedMap R f.map f.over_base f.equivariant
  map_id A := by
    apply (cancel_epi (derivedRestrictionIso A.action A.projection A.over_base R).hom).mp
    rw [← derivedMap_restriction]
    change derivedMap (hp := A.over_base) (hq := A.over_base) (R := R)
        (𝟙 A.space) (by simp) (fun _ => by simp) ≫ _ = _
    rw [derivedMap_id, Category.id_comp, Category.comp_id]
  map_comp {A B C} f k := by
    apply (cancel_epi (derivedRestrictionIso A.action A.projection A.over_base R).hom).mp
    rw [← derivedMap_restriction, ← Category.assoc,
      ← derivedMap_restriction R f.map f.over_base f.equivariant, Category.assoc,
      ← derivedMap_restriction R k.map k.over_base k.equivariant,
      ← Category.assoc, derivedMap_comp]
    rfl

/-- Actual ordinary restriction objects and maps form a functor in both inputs. -/
def restrictionCohomologyConsumer (n : ℕ) :
    EtaleDatum X G ⥤ (ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) G) where
  obj A := deckCohomologyFunctor R A.action A.projection A.over_base n
  map f := restrictionCohomologyMap R f.map f.over_base f.equivariant n
  map_id A := by
    apply (cancel_epi (cohomologyRestrictionIso A.action A.projection A.over_base R n).hom).mp
    rw [← cohomologyMap_restriction]
    change cohomologyMap (hp := A.over_base) (hq := A.over_base) (R := R)
        (𝟙 A.space) (by simp) (fun _ => by simp) n ≫ _ = _
    rw [cohomologyMap_id, Category.id_comp, Category.comp_id]
  map_comp {A B C} f k := by
    apply (cancel_epi (cohomologyRestrictionIso A.action A.projection A.over_base R n).hom).mp
    rw [← cohomologyMap_restriction, ← Category.assoc,
      ← cohomologyMap_restriction R f.map f.over_base f.equivariant n, Category.assoc,
      ← cohomologyMap_restriction R k.map k.over_base k.equivariant n,
      ← Category.assoc, cohomologyMap_comp]
    rfl

/-- Actual restriction sections and maps form a functor in both inputs. -/
def restrictionSectionsConsumer :
    EtaleDatum X G ⥤ (ModuleSheaf X R ⥤ Action (ModuleCat.{u} R) G) where
  obj A := deckSectionsFunctor R A.action A.projection A.over_base
  map f := restrictionSectionsMap R f.map f.over_base f.equivariant
  map_id A := by
    apply (cancel_epi (sectionsRestrictionIso A.action A.projection A.over_base R).hom).mp
    rw [← sectionsMap_restriction]
    change sectionsMap (hp := A.over_base) (hq := A.over_base) (R := R)
        (𝟙 A.space) (by simp) (fun _ => by simp) ≫ _ = _
    rw [sectionsMap_id, Category.id_comp, Category.comp_id]
  map_comp {A B C} f k := by
    apply (cancel_epi (sectionsRestrictionIso A.action A.projection A.over_base R).hom).mp
    rw [← sectionsMap_restriction, ← Category.assoc,
      ← sectionsMap_restriction R f.map f.over_base f.equivariant, Category.assoc,
      ← sectionsMap_restriction R k.map k.over_base k.equivariant,
      ← Category.assoc, sectionsMap_comp]
    rfl

/-- Restriction evaluation retains the original small-etale coefficient sheaf. -/
@[simp] theorem restrictionDerivedConsumer_obj_obj_V (A : EtaleDatum X G)
    (M : ModuleSheaf X R) :
    (((restrictionDerivedConsumer R).obj A).obj M).V =
      (EtaleDerivedSectionsPlus.derivedSections A.space R).obj
        ((restriction A.projection (ModuleCat.{u} R)).obj M) := rfl

@[simp] theorem restrictionCohomologyConsumer_obj_obj_V (n : ℕ) (A : EtaleDatum X G)
    (M : ModuleSheaf X R) :
    (((restrictionCohomologyConsumer R n).obj A).obj M).V =
      (EtaleDerivedSections.cohomology A.space R n).obj
        ((restriction A.projection (ModuleCat.{u} R)).obj M) := rfl

@[simp] theorem restrictionSectionsConsumer_obj_obj_V (A : EtaleDatum X G)
    (M : ModuleSheaf X R) :
    (((restrictionSectionsConsumer R).obj A).obj M).V =
      (EtaleDerivedSections.sections A.space R).obj
        ((restriction A.projection (ModuleCat.{u} R)).obj M) := rfl

/-- The restriction action uses the original automorphism and the exact
restriction composition followed by transport along its deck equation. -/
theorem restrictionDerivedConsumer_obj_obj_ρ (A : EtaleDatum X G)
    (M : ModuleSheaf X R) (g : G) :
    (((restrictionDerivedConsumer R).obj A).obj M).ρ g =
      derivedSectionsMapWithCoefficients (aut A.action g).hom R
        ((restrictionComp A.projection (ModuleCat.{u} R) (aut A.action g).hom).hom.app M ≫
          (restrictionCongr R (A.over_base g)).hom.app M) := by
  change ((deckDerivedSectionsFunctor R A.action A.projection A.over_base).obj M).ρ g = _
  rw [deckDerivedSectionsFunctor_obj_ρ, restrictionCoefficient_act]
  rfl

theorem restrictionCohomologyConsumer_obj_obj_ρ (n : ℕ) (A : EtaleDatum X G)
    (M : ModuleSheaf X R) (g : G) :
    (((restrictionCohomologyConsumer R n).obj A).obj M).ρ g =
      cohomologyMapWithCoefficients (aut A.action g).hom R n
        ((restrictionComp A.projection (ModuleCat.{u} R) (aut A.action g).hom).hom.app M ≫
          (restrictionCongr R (A.over_base g)).hom.app M) := by
  change (pullbackCohomologyAction R A.action
    ((deckEquivariantFunctor R A.action A.projection A.over_base).obj M) n).ρ g = _
  rw [pullbackCohomologyAction_ρ, restrictionCoefficient_act]

theorem restrictionSectionsConsumer_obj_obj_ρ (A : EtaleDatum X G)
    (M : ModuleSheaf X R) (g : G) :
    (((restrictionSectionsConsumer R).obj A).obj M).ρ g =
      (EtalePullback.sectionsMap (aut A.action g).hom R).app
          ((restriction A.projection (ModuleCat.{u} R)).obj M) ≫
        (EtaleDerivedSections.sections A.space R).map
          ((restrictionComp A.projection (ModuleCat.{u} R) (aut A.action g).hom).hom.app M ≫
            (restrictionCongr R (A.over_base g)).hom.app M) := by
  change ((pullbackSectionsFunctor R A.action).obj
    ((deckEquivariantFunctor R A.action A.projection A.over_base).obj M)).ρ g = _
  rw [pullbackSectionsFunctor_obj_ρ, restrictionCoefficient_act]
  rfl

/-- Coefficient arrows are the original restriction maps followed by their
corresponding cohomological consumer. -/
@[simp] theorem restrictionDerivedConsumer_obj_map_hom (A : EtaleDatum X G)
    {M N : ModuleSheaf X R} (α : M ⟶ N) :
    (((restrictionDerivedConsumer R).obj A).map α).hom =
      (EtaleDerivedSectionsPlus.derivedSections A.space R).map
        ((restriction A.projection (ModuleCat.{u} R)).map α) := rfl

@[simp] theorem restrictionCohomologyConsumer_obj_map_hom (n : ℕ) (A : EtaleDatum X G)
    {M N : ModuleSheaf X R} (α : M ⟶ N) :
    (((restrictionCohomologyConsumer R n).obj A).map α).hom =
      (EtaleDerivedSections.cohomology A.space R n).map
        ((restriction A.projection (ModuleCat.{u} R)).map α) := rfl

@[simp] theorem restrictionSectionsConsumer_obj_map_hom (A : EtaleDatum X G)
    {M N : ModuleSheaf X R} (α : M ⟶ N) :
    (((restrictionSectionsConsumer R).obj A).map α).hom =
      (EtaleDerivedSections.sections A.space R).map
        ((restriction A.projection (ModuleCat.{u} R)).map α) :=
  pullbackSectionsFunctor_map_hom R A.action
    ((deckEquivariantFunctor R A.action A.projection A.over_base).map α)

/-- The geometric component is the actual original restriction map with its
original restriction triangle coefficient. -/
@[simp] theorem restrictionDerivedConsumer_map_app_hom {A B : EtaleDatum X G}
    (f : A ⟶ B) (M : ModuleSheaf X R) :
    (((restrictionDerivedConsumer R).map f).app M).hom =
      derivedSectionsMapWithCoefficients f.map R
        ((restrictionComp A.projection (ModuleCat.{u} R) f.map).hom.app M ≫
          (restrictionCongr R f.over_base).hom.app M) :=
  restrictionDerivedMap_app_hom R f.map f.over_base f.equivariant M

@[simp] theorem restrictionCohomologyConsumer_map_app_hom (n : ℕ)
    {A B : EtaleDatum X G} (f : A ⟶ B) (M : ModuleSheaf X R) :
    (((restrictionCohomologyConsumer R n).map f).app M).hom =
      cohomologyMapWithCoefficients f.map R n
        ((restrictionComp A.projection (ModuleCat.{u} R) f.map).hom.app M ≫
          (restrictionCongr R f.over_base).hom.app M) :=
  restrictionCohomologyMap_app_hom R f.map f.over_base f.equivariant n M

@[simp] theorem restrictionSectionsConsumer_map_app_hom {A B : EtaleDatum X G}
    (f : A ⟶ B) (M : ModuleSheaf X R) :
    (((restrictionSectionsConsumer R).map f).app M).hom =
      (EtalePullback.sectionsMap f.map R).app
          ((restriction A.projection (ModuleCat.{u} R)).obj M) ≫
        (EtaleDerivedSections.sections B.space R).map
          ((restrictionComp A.projection (ModuleCat.{u} R) f.map).hom.app M ≫
            (restrictionCongr R f.over_base).hom.app M) :=
  restrictionSectionsMap_app_hom R f.map f.over_base f.equivariant M

/-- The specified derived restriction comparison is natural in geometry and coefficients. -/
def derivedRestrictionConsumerIso :
    derivedConsumer (X := X) (G := G) R ≅ restrictionDerivedConsumer R :=
  NatIso.ofComponents (fun A => derivedRestrictionIso A.action A.projection A.over_base R)
    (by
      intro A B f
      exact derivedMap_restriction R f.map f.over_base f.equivariant)

/-- The specified ordinary comparison is natural in both inputs. -/
def cohomologyRestrictionConsumerIso (n : ℕ) :
    cohomologyConsumer (X := X) (G := G) R n ≅ restrictionCohomologyConsumer R n :=
  NatIso.ofComponents (fun A => cohomologyRestrictionIso A.action A.projection A.over_base R n)
    (by
      intro A B f
      exact cohomologyMap_restriction R f.map f.over_base f.equivariant n)

/-- The specified section comparison is natural in both inputs. -/
def sectionsRestrictionConsumerIso :
    sectionsConsumer (X := X) (G := G) R ≅ restrictionSectionsConsumer R :=
  NatIso.ofComponents (fun A => sectionsRestrictionIso A.action A.projection A.over_base R)
    (by
      intro A B f
      exact sectionsMap_restriction R f.map f.over_base f.equivariant)

set_option maxHeartbeats 600000 in
/-- The canonical specified homology recovery is reused along forgetting. -/
def homologyConsumerIso (n : ℕ) :
    derivedConsumer (X := X) (G := G) R ⋙
        (Functor.whiskeringRight (ModuleSheaf X R)
          (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).mapAction G) ≅
      cohomologyConsumer R n :=
  NatIso.ofComponents (fun A => homologyFunctorIso A.action A.projection A.over_base R n)
    (by
      intro A B f
      exact derivedMap_homology f.map f.over_base f.equivariant n)

set_option maxHeartbeats 600000 in
/-- The canonical specified derived degree-zero recovery is reused along forgetting. -/
def derivedZeroConsumerIso :
    derivedConsumer (X := X) (G := G) R ⋙
        (Functor.whiskeringRight (ModuleSheaf X R)
          (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≅
      sectionsConsumer R :=
  NatIso.ofComponents (fun A => derivedZeroFunctorIso A.action A.projection A.over_base R)
    (by
      intro A B f
      exact derivedMap_zero f.map f.over_base f.equivariant)

set_option maxHeartbeats 600000 in
/-- The canonical specified ordinary degree-zero recovery is reused along forgetting. -/
def cohomologyZeroConsumerIso :
    cohomologyConsumer (X := X) (G := G) R 0 ≅ sectionsConsumer R :=
  NatIso.ofComponents (fun A => cohomologyZeroFunctorIso A.action A.projection A.over_base R)
    (by
      intro A B f
      exact cohomologyMap_zero f.map f.over_base f.equivariant)

/-- The old specified homology recovery is natural in both inputs. -/
def restrictionHomologyConsumerIso (n : ℕ) :
    restrictionDerivedConsumer (X := X) (G := G) R ⋙
        (Functor.whiskeringRight (ModuleSheaf X R)
          (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).mapAction G) ≅
      restrictionCohomologyConsumer R n :=
  NatIso.ofComponents (fun A => deckDerivedHomologyIso R A.action A.projection A.over_base n)
    (fun f => restrictionDerivedMap_homology R f.map f.over_base f.equivariant n)

/-- The old specified derived degree-zero recovery is natural in both inputs. -/
def restrictionDerivedZeroConsumerIso :
    restrictionDerivedConsumer (X := X) (G := G) R ⋙
        (Functor.whiskeringRight (ModuleSheaf X R)
          (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G) ≅
      restrictionSectionsConsumer R :=
  NatIso.ofComponents (fun A => deckDerivedZeroIso R A.action A.projection A.over_base)
    (fun f => restrictionDerivedMap_zero R f.map f.over_base f.equivariant)

/-- The old specified ordinary degree-zero recovery is natural in both inputs. -/
def restrictionCohomologyZeroConsumerIso :
    restrictionCohomologyConsumer (X := X) (G := G) R 0 ≅ restrictionSectionsConsumer R :=
  NatIso.ofComponents (fun A => restrictionCohomologyZeroIso A.action A.projection A.over_base R)
    (fun f => restrictionCohomologyMap_zero R f.map f.over_base f.equivariant)

/-- Each comparison is the corresponding consumer applied to the specified
inverse-image/restriction coefficient comparison at the original geometry. -/
@[simp] theorem derivedRestrictionConsumerIso_hom_app_app_hom (A : EtaleDatum X G)
    (M : ModuleSheaf X R) :
    (((derivedRestrictionConsumerIso R).hom.app A).app M).hom =
      (EtaleDerivedSectionsPlus.derivedSections A.space R).map
        ((inverseImageIsoRestriction A.projection R).hom.app M) :=
  derivedRestrictionIso_hom_app_hom A.action A.projection A.over_base R M

@[simp] theorem cohomologyRestrictionConsumerIso_hom_app_app_hom (n : ℕ)
    (A : EtaleDatum X G) (M : ModuleSheaf X R) :
    (((cohomologyRestrictionConsumerIso R n).hom.app A).app M).hom =
      (EtaleDerivedSections.cohomology A.space R n).map
        ((inverseImageIsoRestriction A.projection R).hom.app M) :=
  cohomologyRestrictionIso_hom_app_hom A.action A.projection A.over_base R n M

@[simp] theorem sectionsRestrictionConsumerIso_hom_app_app_hom (A : EtaleDatum X G)
    (M : ModuleSheaf X R) :
    (((sectionsRestrictionConsumerIso R).hom.app A).app M).hom =
      (EtaleDerivedSections.sections A.space R).map
        ((inverseImageIsoRestriction A.projection R).hom.app M) :=
  sectionsRestrictionIso_hom_app_hom A.action A.projection A.over_base R M

/-- Canonical recovery uses the specified original homology comparison at
the actual inverse-image coefficient. -/
@[simp] theorem homologyConsumerIso_hom_app_app_hom (n : ℕ) (A : EtaleDatum X G)
    (M : ModuleSheaf X R) :
    (((homologyConsumerIso R n).hom.app A).app M).hom =
      (EtaleDerivedSectionsPlus.homologyNatIso A.space R n).hom.app
        ((inverseImage A.projection R).obj M) := rfl

@[simp] theorem derivedZeroConsumerIso_hom_app_app_hom (A : EtaleDatum X G)
    (M : ModuleSheaf X R) :
    (((derivedZeroConsumerIso R).hom.app A).app M).hom =
      (EtaleDerivedSectionsPlus.homologyZeroIso A.space R).hom.app
        ((inverseImage A.projection R).obj M) := rfl

@[simp] theorem cohomologyZeroConsumerIso_hom_app_app_hom (A : EtaleDatum X G)
    (M : ModuleSheaf X R) :
    (((cohomologyZeroConsumerIso R).hom.app A).app M).hom =
      (EtaleDerivedSectionsPlus.homologyNatIso A.space R 0).inv.app
          ((inverseImage A.projection R).obj M) ≫
        (EtaleDerivedSectionsPlus.homologyZeroIso A.space R).hom.app
          ((inverseImage A.projection R).obj M) := rfl

/-- Restriction recovery retains the specified comparisons at the actual
restriction coefficient, with no free choice of recovery isomorphism. -/
@[simp] theorem restrictionHomologyConsumerIso_hom_app_app_hom (n : ℕ)
    (A : EtaleDatum X G) (M : ModuleSheaf X R) :
    (((restrictionHomologyConsumerIso R n).hom.app A).app M).hom =
      (EtaleDerivedSectionsPlus.homologyNatIso A.space R n).hom.app
        ((restriction A.projection (ModuleCat.{u} R)).obj M) := by
  change 𝟙 _ ≫ _ = _
  exact Category.id_comp _

@[simp] theorem restrictionDerivedZeroConsumerIso_hom_app_app_hom (A : EtaleDatum X G)
    (M : ModuleSheaf X R) :
    (((restrictionDerivedZeroConsumerIso R).hom.app A).app M).hom =
      (EtaleDerivedSectionsPlus.homologyZeroIso A.space R).hom.app
        ((restriction A.projection (ModuleCat.{u} R)).obj M) := by
  change 𝟙 _ ≫ ((pullbackDerivedZeroFunctorIso R A.action).hom.app
    ((deckEquivariantFunctor R A.action A.projection A.over_base).obj M)).hom = _
  rw [Category.id_comp, pullbackDerivedZeroFunctorIso_hom_app_hom]
  rfl

@[simp] theorem restrictionCohomologyZeroConsumerIso_hom_app_app_hom
    (A : EtaleDatum X G) (M : ModuleSheaf X R) :
    (((restrictionCohomologyZeroConsumerIso R).hom.app A).app M).hom =
      (EtaleDerivedSections.cohomologyZeroIso A.space R).hom.app
        ((restriction A.projection (ModuleCat.{u} R)).obj M) :=
  restrictionCohomologyZeroIso_hom_app_hom A.action A.projection A.over_base R M

/-- The full two-input derived comparison preserves the specified homology recovery. -/
theorem derivedRestrictionConsumerIso_homology (n : ℕ) :
    Functor.whiskerRight (derivedRestrictionConsumerIso (X := X) (G := G) R).hom
        ((Functor.whiskeringRight (ModuleSheaf X R)
          (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) n).mapAction G)) ≫
      (restrictionHomologyConsumerIso R n).hom =
    (homologyConsumerIso R n).hom ≫ (cohomologyRestrictionConsumerIso R n).hom := by
  apply NatTrans.ext
  funext A
  exact derivedRestrictionIso_homology A.action A.projection A.over_base R n

/-- The full two-input comparison preserves the specified derived degree-zero recovery. -/
theorem derivedRestrictionConsumerIso_zero :
    Functor.whiskerRight (derivedRestrictionConsumerIso (X := X) (G := G) R).hom
        ((Functor.whiskeringRight (ModuleSheaf X R)
          (Action (DerivedCategory.Plus (ModuleCat.{u} R)) G)
          (Action (ModuleCat.{u} R) G)).obj
          ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} R) 0).mapAction G)) ≫
      (restrictionDerivedZeroConsumerIso R).hom =
    (derivedZeroConsumerIso R).hom ≫ (sectionsRestrictionConsumerIso R).hom := by
  apply NatTrans.ext
  funext A
  exact derivedRestrictionIso_zero A.action A.projection A.over_base R

/-- Ordinary degree-zero recovery is preserved as a full two-input square. -/
theorem cohomologyRestrictionConsumerIso_zero :
    (cohomologyRestrictionConsumerIso (X := X) (G := G) R 0).hom ≫
      (restrictionCohomologyZeroConsumerIso R).hom =
    (cohomologyZeroConsumerIso R).hom ≫ (sectionsRestrictionConsumerIso R).hom := by
  apply NatTrans.ext
  funext A
  exact cohomologyRestrictionIso_zero A.action A.projection A.over_base R

end EtaleDatum

end Langlands.Geometry.EtaleSchemeDeckAction
