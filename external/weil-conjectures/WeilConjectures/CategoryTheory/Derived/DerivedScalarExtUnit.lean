/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import WeilConjectures.AlgebraicGeometry.ExactFunctorDerivedUnit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Derived units represented by Ext classes
(blueprint: def-sp-derived-scalar-ext-unit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uC uB vC vB wC wB wE
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- Let U:A→B be exact additive between abelian categories with unbounded derived categories and Ext
[def-weil-abstract-derived-category]. For F in B, H in A, n≥0 and e∈Ext^n(F,UH), define
DerivedExtUnit to mean that e, the inverse single comparison and the inverse commutation with shift
induce bijections Hom((single H)[n],K)→Hom(single F,DU(K)) for every unbounded complex K.
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: def-sp-derived-scalar-ext-unit).
Proof: The three comparisons have composable endpoints. This is the ordinary derived adjunction
universal property, expressed at a degree-n Ext representative and with the existing positive shift
convention. -/
def DerivedExtUnit
    {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B] [HasExt.{wE} B]
    (U : C ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (F : B) (H : C) (n : ℕ) (e : Ext.{wE} F (U.obj H) n) : Prop :=
  ∀ K : DerivedCategory C,
    Function.Bijective (fun f : ((DerivedCategory.singleFunctor C 0).obj H)⟦(n : ℤ)⟧ ⟶ K ↦
      e.hom ≫ ((U.mapDerivedCategorySingleFunctor 0).inv.app H)⟦(n : ℤ)⟧' ≫
        (U.mapDerivedCategory.commShiftIso (n : ℤ)).inv.app
          ((DerivedCategory.singleFunctor C 0).obj H) ≫ U.mapDerivedCategory.map f)

end CategoryTheory.Functor
