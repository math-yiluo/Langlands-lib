/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Degree bounds along distinguished triangles in derived categories

For a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` in the derived category of an abelian
category:

* `DerivedCategory.isLE_obj₃_of_isLE`: if `X₁` and `X₂` lie in degrees `≤ n`, so does `X₃`;
* `DerivedCategory.isGE_obj₃_of_isGE`: if `X₁` and `X₂` lie in degrees `≥ n`, then `X₃` lies in
  degrees `≥ n - 1`.
-/

@[expose] public section

open CategoryTheory Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` of a derived category, if `X₁` and `X₂`
lie in degrees `≤ n`, so does `X₃`. -/
lemma isLE_obj₃_of_isLE (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n : ℤ)
    (h₁ : T.obj₁.IsLE n) (h₂ : T.obj₂.IsLE n) : T.obj₃.IsLE n := by
  have h : ((shiftFunctor (DerivedCategory C) (1 : ℤ)).obj T.obj₁).IsLE n := by
    have := DerivedCategory.TStructure.t.isLE_shift T.obj₁ n 1 (n - 1) (by lia)
    exact DerivedCategory.TStructure.t.isLE_of_le _ (n - 1) n (by lia)
  exact DerivedCategory.TStructure.t.isLE₂ _ (rot_of_distTriang _ hT) n h₂ h

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` of a derived category, if `X₁` and `X₂`
lie in degrees `≥ n`, then `X₃` lies in degrees `≥ n - 1`. -/
lemma isGE_obj₃_of_isGE (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _) (n : ℤ)
    (h₁ : T.obj₁.IsGE n) (h₂ : T.obj₂.IsGE n) : T.obj₃.IsGE (n - 1) := by
  have h : ((shiftFunctor (DerivedCategory C) (1 : ℤ)).obj T.obj₁).IsGE (n - 1) :=
    DerivedCategory.TStructure.t.isGE_shift T.obj₁ n 1 (n - 1) (by lia)
  exact DerivedCategory.TStructure.t.isGE₂ _ (rot_of_distTriang _ hT) (n - 1)
    (DerivedCategory.TStructure.t.isGE_of_ge T.obj₂ (n - 1) n (by lia)) h

end DerivedCategory
