/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-! # The shifted degree-zero comparison for the right derived functor

Source: Stacks Project, derived.tex, Tags 015J and 015N.
-/

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]

/-- Identify degree-n derived cohomology of an object placed in degree n with its image
under the left exact functor. The construction shifts to degree zero, commutes the derived
functor with the shift, and uses the classical degree-zero comparison.
Source: Stacks Project, derived.tex, Tag 015J, proof, remark (1).
(blueprint: def-pc-right-derived-single-degree-comparison) -/
noncomputable def rightDerivedSingleDegreeComparison (n : ℕ) :
    DerivedCategory.Plus.singleFunctor B n ⋙ G.rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.homologyFunctor C n ≅ G := by
  let H₀ := DerivedCategory.Plus.homologyFunctor C 0
  let RG := G.rightDerivedFunctorPlus
  exact Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors B).shiftIso (-(n : ℤ)) n 0 (by simp)).symm
      (RG ⋙ H₀.shift (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor B 0)
      (Functor.isoWhiskerRight (RG.commShiftIso (-(n : ℤ))) (H₀.shift (n : ℤ))) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor B 0 ⋙ RG)
      (H₀.shiftIso (-(n : ℤ)) (n : ℤ) 0 (by ring)) ≪≫
    G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0 ≪≫
    G.rightDerivedZeroIsoSelf

end CategoryTheory.Functor
