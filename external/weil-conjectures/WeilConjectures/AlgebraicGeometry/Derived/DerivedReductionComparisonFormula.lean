/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The representative equation for derived reduction comparisons

Source: Stacks Project, Tags 06YS and 06YY
(blueprint: def-weil-pbc-derived-reduction-comparison-formula).

The predicate records the ordinary comparison transported through the two specified
reduction counits and the localization factors of exact pullback. Naming the common
formula lets applications share its categorical data without unfolding concrete module
categories and functors during every conversion.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The counit-normalized comparison on a cochain representative.
Source: Stacks Project, Tags 06YS and 06YY
(blueprint: def-weil-pbc-derived-reduction-comparison-formula). -/
def DerivedReductionComparisonFormula
    {B C D E : Type*} [Category B] [Category C] [Category D] [Category E]
    [Abelian B] [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory E]
    (F : B ⥤ C) (G : D ⥤ E) (RX : B ⥤ D) (RY : C ⥤ E)
    [F.Additive] [G.Additive] [RX.Additive] [RY.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (MY : DerivedCategory B ⥤ DerivedCategory D)
    (MX : DerivedCategory C ⥤ DerivedCategory E)
    (cX : ∀ P : CochainComplex B ℤ, MY.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((RX.mapHomologicalComplex (.up ℤ)).obj P))
    (cY : ∀ P : CochainComplex C ℤ, MX.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((RY.mapHomologicalComplex (.up ℤ)).obj P))
    (e : RX ⋙ G ≅ F ⋙ RY)
    (τ : MY ⋙ G.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ MX)
    (P : CochainComplex B ℤ) : Prop :=
  τ.hom.app (DerivedCategory.Q.obj P) ≫
      MX.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      cY ((F.mapHomologicalComplex (.up ℤ)).obj P) =
    G.mapDerivedCategory.map (cX P) ≫
      G.mapDerivedCategoryFactors.hom.app ((RX.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P)

end AlgebraicGeometry.Scheme
