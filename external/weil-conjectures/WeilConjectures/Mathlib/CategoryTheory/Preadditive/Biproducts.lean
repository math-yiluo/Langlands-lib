/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Basic.Finite.Sum

/-!
# Biproducts indexed by a sum type

For a family `f : J ⊕ K → C` of objects of a preadditive category, the biproduct `⨁ f` is the
binary biproduct of the biproducts of the two restrictions of `f`.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C] {J K : Type} [Finite J] [Finite K]

/-- The biproduct over `J ⊕ K` is the binary biproduct of the biproducts over `J` and `K`. -/
noncomputable def biprodBiproductSumIso (f : J ⊕ K → C) :
    (⨁ fun j ↦ f (.inl j)) ⊞ (⨁ fun k ↦ f (.inr k)) ≅ ⨁ f where
  hom := biprod.desc (biproduct.desc fun j ↦ biproduct.ι f (.inl j))
    (biproduct.desc fun k ↦ biproduct.ι f (.inr k))
  inv := biproduct.desc fun t ↦ Sum.rec (motive := fun t ↦ f t ⟶ _)
    (fun j ↦ biproduct.ι (fun j ↦ f (.inl j)) j ≫ biprod.inl)
    (fun k ↦ biproduct.ι (fun k ↦ f (.inr k)) k ≫ biprod.inr) t
  hom_inv_id := by
    ext <;> simp
  inv_hom_id := by
    ext (j | k) (j' | k') <;> simp

end CategoryTheory.Limits
