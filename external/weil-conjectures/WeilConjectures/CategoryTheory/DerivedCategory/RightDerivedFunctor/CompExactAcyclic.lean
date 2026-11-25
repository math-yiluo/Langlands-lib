/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology

/-!
# Right derived functors of a composite with an exact functor sending injectives to acyclics

If `F : C ⥤ D` is exact and sends injective objects to `G`-acyclic objects, then for every left
exact `G : D ⥤ E` the classical right derived functors satisfy `R^n (F ⋙ G) ≅ F ⋙ R^n G`
(`CategoryTheory.Functor.rightDerivedCompIsoOfExactOfRightAcyclic`): an injective resolution of
`X` is sent by `F` to a `G`-acyclic resolution of `F X`. This generalizes
`CategoryTheory.Functor.rightDerivedCompIsoOfExact`, where `F` preserves injective objects; it
applies to the forgetful functor from sheaves of modules over any ring to abelian sheaves.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits G]

/-- For `F` exact sending injective objects to `G`-acyclic objects, and `G` left exact,
`R^n (F ⋙ G) ≅ F ⋙ R^n G`. -/
noncomputable def rightDerivedCompIsoOfExactOfRightAcyclic
    (hFG : ∀ (I : C) [Injective I], G.rightAcyclic (F.obj I)) (n : ℕ) :
    (F ⋙ G).rightDerived n ≅ F ⋙ G.rightDerived n :=
  ((F ⋙ G).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n).symm ≪≫
    isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      (isoWhiskerRight (rightDerivedFunctorPlusCompIsoOfRightAcyclic F G hFG)
        (DerivedCategory.Plus.homologyFunctor E n) ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus F) ≪≫
      F.mapDerivedCategoryPlusSingleFunctor 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft F (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n)

end CategoryTheory.Functor
