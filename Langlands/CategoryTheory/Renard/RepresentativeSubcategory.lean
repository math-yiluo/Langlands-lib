import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Skeletal

/-!
# Renard A.II.2: a full subcategory of chosen representatives

The objects are actual objects of the ambient category chosen by Mathlib's
skeleton construction. The morphisms are all ambient morphisms between them.
This module constructs the subcategory, its inclusion and representatives,
with the intrinsic uniqueness law. The quasi-inverse comparison is separate.
-/

universe v u

open CategoryTheory

namespace Langlands.Renard

variable (C : Type u) [Category.{v} C]

/-- The actual objects selected as representatives of isomorphism classes. -/
noncomputable def representativeObjects : ObjectProperty C :=
  fun X => ∃ s : Skeleton C, (fromSkeleton C).obj s = X

/-- The full subcategory on the chosen representatives. -/
noncomputable abbrev RepresentativeSubcategory :=
  (representativeObjects C).FullSubcategory

/-- The actual full-subcategory inclusion. -/
noncomputable abbrev representativeInclusion : RepresentativeSubcategory C ⥤ C :=
  (representativeObjects C).ι

variable {C}

/-- The chosen representative of an ambient object, in the full subcategory. -/
noncomputable def representativeOf (X : C) : RepresentativeSubcategory C :=
  ⟨(fromSkeleton C).obj (toSkeleton X), ⟨toSkeleton X, rfl⟩⟩

/-- The selected representative is actually isomorphic to the original object. -/
noncomputable def representativeIso (X : C) :
    (representativeInclusion C).obj (representativeOf X) ≅ X :=
  fromSkeletonToSkeletonIso X

/-- Two selected representatives that are isomorphic are equal as objects
of the full subcategory. -/
theorem representative_eq_of_iso {X Y : RepresentativeSubcategory C}
    (e : X.obj ≅ Y.obj) : X = Y := by
  obtain ⟨sX, hX⟩ := X.property
  obtain ⟨sY, hY⟩ := Y.property
  have hs : sX = sY := by
    rw [← toSkeleton_fromSkeleton_obj sX, ← toSkeleton_fromSkeleton_obj sY]
    exact congr_toSkeleton_of_iso
      (eqToIso hX ≪≫ e ≪≫ (eqToIso hY).symm)
  apply ObjectProperty.FullSubcategory.ext
  exact hX.symm.trans ((congrArg (fromSkeleton C).obj hs).trans hY)

end Langlands.Renard
