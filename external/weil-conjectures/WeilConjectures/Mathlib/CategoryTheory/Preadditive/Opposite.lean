/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Additive functors out of the opposite category and biproducts

An additive functor `F : Cᵒᵖ ⥤ D` sends a finite biproduct `⨁ f` of `C` to the biproduct of the
`F (f j)` (`CategoryTheory.Functor.opMapBiproductIso`): the images of the projections and
inclusions of `⨁ f` form a bilimit bicone.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive D] (F : Cᵒᵖ ⥤ D) [F.Additive] {J : Type w} [Fintype J] (f : J → C)
  [HasBiproduct f]

namespace Functor

/-- The image of the biproduct bicone of `f` under an additive functor `F : Cᵒᵖ ⥤ D`: its
projections are the images of the inclusions of `⨁ f` and vice versa. -/
@[simps]
noncomputable def opMapBicone : Bicone fun j ↦ F.obj (op (f j)) where
  pt := F.obj (op (⨁ f))
  π j := F.map (biproduct.ι f j).op
  ι j := F.map (biproduct.π f j).op
  ι_π j j' := by
    classical
    rw [← F.map_comp, ← op_comp]
    by_cases h : j = j'
    · subst h
      simp
    · rw [biproduct.ι_π_ne _ (Ne.symm h), dite_eq_right h, op_zero, F.map_zero]

/-- The image of the biproduct bicone of `f` under an additive functor `F : Cᵒᵖ ⥤ D` is a
bilimit bicone. -/
noncomputable def isBilimitOpMapBicone : (F.opMapBicone f).IsBilimit :=
  isBilimitOfTotal _ (by
    change ∑ j, F.map (biproduct.ι f j).op ≫ F.map (biproduct.π f j).op = 𝟙 (F.obj (op (⨁ f)))
    simp_rw [← F.map_comp, ← op_comp]
    rw [← F.map_sum, ← op_sum, IsBilimit.total (biproduct.isBilimit f), op_id, F.map_id])

variable [HasBiproduct fun j ↦ F.obj (op (f j))]

/-- An additive functor `F : Cᵒᵖ ⥤ D` sends the biproduct `⨁ f` to the biproduct of the
`F (f j)`. -/
noncomputable def opMapBiproductIso : F.obj (op (⨁ f)) ≅ ⨁ fun j ↦ F.obj (op (f j)) :=
  biproduct.uniqueUpToIso _ (F.isBilimitOpMapBicone f)

end Functor

end CategoryTheory
