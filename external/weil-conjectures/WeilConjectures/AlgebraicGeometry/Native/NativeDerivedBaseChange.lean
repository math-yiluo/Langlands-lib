/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The ordinary native derived exchange map
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

namespace ProEtale

/-- The exact pullback comparison on ordinary native derived categories, obtained by
localizing the actual composition comparison. -/
def adicDerivedPullSquare (l : ℕ) [Fact l.Prime]
    {Z' Z T' T : Scheme.{u}} {v : Z' ⟶ Z} {p' : Z' ⟶ T'}
    {p : Z ⟶ T} {g : T' ⟶ T} (sq : CommSq v p' p g) :
    (adicUpperStar l g).mapDerivedCategory ⋙ (adicUpperStar l p').mapDerivedCategory ≅
      (adicUpperStar l p).mapDerivedCategory ⋙ (adicUpperStar l v).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso (adicUpperStarCompIso l sq.w.symm) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The unit--square--counit mate on ordinary native geometric derived categories.
No boundedness, properness, or Weil structure is needed to construct it. -/
def adicDerivedBaseChange (l : ℕ) [Fact l.Prime]
    {Z' Z T' T : Scheme.{u}} {v : Z' ⟶ Z} {p' : Z' ⟶ T'}
    {p : Z ⟶ T} {g : T' ⟶ T} (sq : CommSq v p' p g) :
    (adicLowerStar l p).rightDerivedFunctor ⋙ (adicUpperStar l g).mapDerivedCategory ⟶
      (adicUpperStar l v).mapDerivedCategory ⋙ (adicLowerStar l p').rightDerivedFunctor :=
  (mateEquiv
    (adicUpperStarLowerStarAdjunction l p).mapDerivedCategoryRightDerivedAdjunction
    (adicUpperStarLowerStarAdjunction l p').mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (adicDerivedPullSquare l sq).hom))

end ProEtale

end AlgebraicGeometry
