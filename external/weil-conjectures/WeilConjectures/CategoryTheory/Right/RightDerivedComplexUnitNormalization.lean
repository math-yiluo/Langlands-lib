/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback

/-!
# Removing the identity homotopy factor from the complex derived unit

Source: the canonical quotient and right-derived unit constructions.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory

namespace CategoryTheory.Functor

/-- The explicit homotopy-factor comparison in the complex derived unit is identity.
Source: the definitions of mapHomotopyCategoryFactors and rightDerivedFunctorUnitQ.
(blueprint: lem-pbc-right-derived-complex-unit-normalization).
Proof: the inverse homotopy-factor comparison is identity by construction. Its image
under Qh is identity, so deleting that factor gives the canonical complex unit. -/
theorem rightDerivedComplexUnitNormalization
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (K : CochainComplex C ℤ) :
    (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
        DerivedCategory.Qh.map ((F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K) ≫
        F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
        F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso C).hom.app K) =
      F.rightDerivedFunctorUnitQ K := by
  have hid : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  rw [hid]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end CategoryTheory.Functor
