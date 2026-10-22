import Mathlib.CategoryTheory.Monoidal.Skeleton
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# Picard groups of braided monoidal categories

The Picard group is the additive group of units in the monoid of isomorphism classes.
-/

noncomputable section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Langlands.CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- An object has a tensor inverse on the right. In a braided category this is two-sided. -/
def TensorInvertible (X : C) : Prop := ∃ Y : C, Nonempty (X ⊗ Y ≅ 𝟙_ C)

namespace TensorInvertible

lemma unit : TensorInvertible (𝟙_ C) := ⟨𝟙_ C, ⟨λ_ (𝟙_ C)⟩⟩

lemma of_iso {X Y : C} (e : X ≅ Y) (hX : TensorInvertible X) : TensorInvertible Y := by
  obtain ⟨Z, ⟨i⟩⟩ := hX
  exact ⟨Z, ⟨(e.symm ⊗ᵢ Iso.refl Z) ≪≫ i⟩⟩

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

lemma map (F : C ⥤ D) [F.Monoidal] {X : C} (hX : TensorInvertible X) :
    TensorInvertible (F.obj X) := by
  obtain ⟨Y, ⟨e⟩⟩ := hX
  exact ⟨F.obj Y, ⟨Functor.Monoidal.μIso F X Y ≪≫ F.mapIso e ≪≫
    (Functor.Monoidal.εIso F).symm⟩⟩

end TensorInvertible

variable [BraidedCategory C]

/-- Tensor-invertible objects are exactly the units of the skeleton monoid. -/
lemma tensorInvertible_iff_isUnit (X : C) :
    TensorInvertible X ↔ IsUnit (toSkeleton X) := by
  rw [isUnit_iff_exists_inv]
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    refine ⟨toSkeleton Y, ?_⟩
    rw [← Skeleton.toSkeleton_tensorObj]
    exact congr_toSkeleton_of_iso e
  · rintro ⟨Y, hY⟩
    refine ⟨(fromSkeleton C).obj Y, ?_⟩
    apply toSkeleton_eq_toSkeleton_iff.mp
    rw [Skeleton.toSkeleton_tensorObj, toSkeleton_fromSkeleton_obj]
    exact hY

lemma TensorInvertible.tensor {X Y : C} (hX : TensorInvertible X)
    (hY : TensorInvertible Y) : TensorInvertible (X ⊗ Y) := by
  rw [tensorInvertible_iff_isUnit, Skeleton.toSkeleton_tensorObj]
  exact ((tensorInvertible_iff_isUnit X).mp hX).mul
    ((tensorInvertible_iff_isUnit Y).mp hY)

/-- Isomorphism classes of tensor-invertible objects, with tensor product written additively. -/
abbrev PicardGroup (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] :=
  Additive ((Skeleton C)ˣ)

namespace PicardGroup

/-- The class of a tensor-invertible object. -/
def ofObject (X : C) (hX : TensorInvertible X) : PicardGroup C :=
  Additive.ofMul ((tensorInvertible_iff_isUnit X).mp hX).unit

/-- The underlying isomorphism class. -/
def toSkeletonClass (x : PicardGroup C) : Skeleton C := x.toMul.val

@[simp] lemma toSkeletonClass_ofObject (X : C) (hX : TensorInvertible X) :
    toSkeletonClass (ofObject X hX) = toSkeleton X :=
  IsUnit.unit_spec _

lemma toSkeletonClass_injective :
    Function.Injective (toSkeletonClass : PicardGroup C → Skeleton C) := by
  intro x y h
  exact Additive.toMul.injective (Units.ext h)

@[ext] lemma ext {x y : PicardGroup C} (h : toSkeletonClass x = toSkeletonClass y) : x = y :=
  toSkeletonClass_injective h

/-- A chosen representative of a Picard class. -/
def representative (x : PicardGroup C) : C := (fromSkeleton C).obj (toSkeletonClass x)

@[simp] lemma toSkeleton_representative (x : PicardGroup C) :
    toSkeleton (representative x) = toSkeletonClass x := toSkeleton_fromSkeleton_obj _

lemma representative_invertible (x : PicardGroup C) : TensorInvertible (representative x) := by
  rw [tensorInvertible_iff_isUnit, toSkeleton_representative]
  exact x.toMul.isUnit

@[simp] lemma ofObject_representative (x : PicardGroup C) :
    ofObject (representative x) (representative_invertible x) = x := by
  apply ext
  simp

lemma ofObject_eq_iff (X Y : C) (hX : TensorInvertible X) (hY : TensorInvertible Y) :
    ofObject X hX = ofObject Y hY ↔ Nonempty (X ≅ Y) := by
  rw [← toSkeletonClass_injective.eq_iff, toSkeletonClass_ofObject, toSkeletonClass_ofObject]
  exact toSkeleton_eq_toSkeleton_iff

lemma eq_iff (x y : PicardGroup C) :
    x = y ↔ Nonempty (representative x ≅ representative y) := by
  rw [← toSkeleton_eq_toSkeleton_iff, toSkeleton_representative,
    toSkeleton_representative]
  exact toSkeletonClass_injective.eq_iff.symm

@[simp] lemma toSkeletonClass_zero : toSkeletonClass (0 : PicardGroup C) = toSkeleton (𝟙_ C) := rfl

@[simp] lemma toSkeletonClass_add (x y : PicardGroup C) :
    toSkeletonClass (x + y) = toSkeletonClass x * toSkeletonClass y := rfl

@[simp] lemma toSkeletonClass_neg (x : PicardGroup C) : toSkeletonClass (-x) = ↑(x.toMul⁻¹) := rfl

@[simp] lemma ofObject_unit : ofObject (𝟙_ C) TensorInvertible.unit = (0 : PicardGroup C) := by
  apply ext
  simp

lemma ofObject_tensor (X Y : C) (hX : TensorInvertible X) (hY : TensorInvertible Y) :
    ofObject (X ⊗ Y) (hX.tensor hY) = ofObject X hX + ofObject Y hY := by
  apply ext
  simp [Skeleton.toSkeleton_tensorObj]

/-- A chosen representative of the negative class is a tensor inverse. -/
def representativeTensorNegIso (x : PicardGroup C) :
    representative x ⊗ representative (-x) ≅ 𝟙_ C :=
  Skeleton.isoOfEq (by
    rw [Skeleton.toSkeleton_tensorObj, toSkeleton_representative,
      toSkeleton_representative]
    exact x.toMul.val_inv)

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]

/-- The additive homomorphism induced by a strong monoidal functor. -/
def map (F : C ⥤ D) [F.Monoidal] : PicardGroup C →+ PicardGroup D :=
  (Units.map (Skeleton.monoidHom F)).toAdditive

@[simp] lemma toSkeletonClass_map (F : C ⥤ D) [F.Monoidal] (x : PicardGroup C) :
    toSkeletonClass (map F x) = F.mapSkeleton.obj (toSkeletonClass x) := rfl

@[simp] lemma map_ofObject (F : C ⥤ D) [F.Monoidal] (X : C) (hX : TensorInvertible X) :
    map F (ofObject X hX) = ofObject (F.obj X) (hX.map F) := by
  apply ext
  simp [Functor.mapSkeleton_obj_toSkeleton]

end PicardGroup
end Langlands.CategoryTheory
