import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.RingTheory.Localization.Basic

/-! # Ring-denominator pairs and the canonical localization structured arrow -/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Renard.RingLocalization

universe u

/-- An actual commutative unital ring with a designated denominator submonoid. -/
structure RingPair where
  ring : CommRingCat.{u}
  denominators : Submonoid ring

/-- Maps preserve both the unital ring structure and the designated denominators. -/
@[ext] structure Hom (A B : RingPair.{u}) where
  raw : A.ring →+* B.ring
  preserves : ∀ s : A.ring, s ∈ A.denominators → raw s ∈ B.denominators

instance : Category.{u} RingPair.{u} where
  Hom A B := Hom A B
  id A := ⟨RingHom.id A.ring, fun _ hs => hs⟩
  comp f g := ⟨g.raw.comp f.raw, fun s hs => g.preserves (f.raw s) (f.preserves s hs)⟩
  id_comp := by intro A B f; apply Hom.ext; rfl
  comp_id := by intro A B f; apply Hom.ext; rfl
  assoc := by intro A B C D f g h; apply Hom.ext; rfl

/-- Forget only the designated denominator submonoid. -/
def forgetToCommRing : RingPair.{u} ⥤ CommRingCat.{u} where
  obj A := A.ring
  map f := CommRingCat.ofHom f.raw

/-- The source locality condition on actual ring-denominator pairs. -/
def localRingProperty : ObjectProperty RingPair.{u} :=
  fun A => ∀ s : A.ring, s ∈ A.denominators → IsUnit s

/-- The actual full subcategory whose designated denominators are units. -/
abbrev LocalRingCat := localRingProperty.{u}.FullSubcategory

/-- Inclusion retaining every denominator-preserving unital ring map. -/
abbrev localRingInclusion : LocalRingCat.{u} ⥤ RingPair.{u} :=
  localRingProperty.{u}.ι

/-- The inclusion is fully faithful by construction of the full subcategory. -/
abbrev localRingInclusionFullyFaithful : localRingInclusion.{u}.FullyFaithful :=
  localRingProperty.{u}.fullyFaithfulι

/-- The actual localization, designating precisely the image of the original submonoid. -/
def canonicalPair (A : RingPair.{u}) : RingPair.{u} where
  ring := CommRingCat.of (Localization A.denominators)
  denominators := A.denominators.map (algebraMap A.ring (Localization A.denominators))

/-- The designated image consists of units in the actual localization. -/
def canonicalLocalObject (A : RingPair.{u}) : LocalRingCat.{u} :=
  ⟨canonicalPair A, by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hs
    exact IsLocalization.map_units (Localization A.denominators) ⟨a, ha⟩⟩

/-- The actual canonical ring map, preserving the designated submonoids. -/
def canonicalRingMap (A : RingPair.{u}) :
    A ⟶ localRingInclusion.obj (canonicalLocalObject A) where
  raw := algebraMap A.ring (Localization A.denominators)
  preserves _ hs := Submonoid.mem_map_of_mem _ hs

/-- The canonical candidate for the source's right universal arrow. -/
def canonicalStructuredArrow (A : RingPair.{u}) :
    StructuredArrow A localRingInclusion.{u} :=
  StructuredArrow.mk (canonicalRingMap A)

/-- On the underlying ring the canonical map is precisely the actual algebra map. -/
@[simp] theorem canonicalRingMap_apply (A : RingPair.{u}) (a : A.ring) :
    (canonicalRingMap A).raw a = algebraMap A.ring (Localization A.denominators) a :=
  rfl

/-- The factor candidate uses the actual ring-localization lift.
Its categorical universal property is a separate obligation. -/
def canonicalFactor (A : RingPair.{u}) (N : LocalRingCat.{u}) (f : A ⟶ N.obj) :
    canonicalLocalObject A ⟶ N :=
  ObjectProperty.homMk
    { raw := IsLocalization.lift (S := Localization A.denominators) (g := f.raw)
        (fun s => N.property (f.raw s) (f.preserves s s.property))
      preserves := by
        intro s hs
        obtain ⟨a, ha, rfl⟩ := Submonoid.mem_map.mp hs
        change (IsLocalization.lift (S := Localization A.denominators) (g := f.raw) _)
          (algebraMap A.ring (Localization A.denominators) a) ∈ N.obj.denominators
        rw [IsLocalization.lift_eq]
        exact f.preserves a ha }

/-- The underlying factor evaluates on the original ring by the given map. -/
@[simp] theorem canonicalFactor_algebraMap (A : RingPair.{u}) (N : LocalRingCat.{u})
    (f : A ⟶ N.obj) (a : A.ring) :
    (canonicalFactor A N f).hom.raw
      (algebraMap A.ring (Localization A.denominators) a) = f.raw a := by
  change (IsLocalization.lift (S := Localization A.denominators) (g := f.raw) _)
    (algebraMap A.ring (Localization A.denominators) a) = f.raw a
  exact IsLocalization.lift_eq _ a

/-- If zero is designated, the underlying actual localized ring is the zero ring. -/
theorem canonicalLocalObject_subsingleton (A : RingPair.{u})
    (h0 : (0 : A.ring) ∈ A.denominators) :
    Subsingleton (canonicalLocalObject A).obj.ring := by
  change Subsingleton (Localization A.denominators)
  exact IsLocalization.subsingleton (S := Localization A.denominators) h0

end Langlands.Renard.RingLocalization
