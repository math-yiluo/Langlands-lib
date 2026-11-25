/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Right derived functors of a composite with an exact functor

If `F : C ⥤ D` is exact and preserves injective objects, then for every additive `G : D ⥤ E`
the classical right derived functors satisfy `R^n (F ⋙ G) ≅ F ⋙ R^n G`
(`CategoryTheory.Functor.rightDerivedCompIsoOfExact`): an injective resolution of `X` is sent by
`F` to an injective resolution of `F X`.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesInjectiveObjects]

/-- For `F` exact and preserving injective objects, `R^n (F ⋙ G) ≅ F ⋙ R^n G`. -/
noncomputable def rightDerivedCompIsoOfExact (n : ℕ) :
    (F ⋙ G).rightDerived n ≅ F ⋙ G.rightDerived n :=
  ((F ⋙ G).singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n).symm ≪≫
    isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      (isoWhiskerRight (rightDerivedFunctorPlusCompIso F G)
        (DerivedCategory.Plus.homologyFunctor E n) ≪≫ Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      (rightDerivedFunctorPlusIsoMapDerivedCategoryPlus F) ≪≫
      F.mapDerivedCategoryPlusSingleFunctor 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft F (G.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso n)

end CategoryTheory.Functor
