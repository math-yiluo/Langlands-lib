/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompExact

/-!
# The counit of `L(f) ⋙ D(g)` for an exact functor `g`, without associators

For an exact functor `g`, `L(f) ⋙ D(g)` is a total left derived functor of `f ⋙ g`. This file
gives the counit `Qh ⋙ L(f) ⋙ D(g) ⟶ (f ⋙ g).mapHomotopyCategory ⋙ Qh` exhibiting it, as the
plain composite of the counit of `L(f)` and the identification of `D(g)` with `g` applied
levelwise (without the associators of
`Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit`).

Stating this once for arbitrary categories keeps the kernel from checking the functor
compositions at concrete categories, where they unfold to the concrete derived categories.

## Main definitions and results

- `CategoryTheory.Functor.leftDerivedFunctorCompExactCounit`: the counit.
- `CategoryTheory.Functor.isLeftDerivedFunctor_leftDerivedFunctorCompExactCounit`: it exhibits
  `L(f) ⋙ D(g)` as a left derived functor of `f ⋙ g`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

section LeftDerivedCompMapDerivedCategory

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (f : C ⥤ D) (g : D ⥤ C) [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

/-- The counit exhibiting `L(f) ⋙ D(g)` as a total left derived functor of `f ⋙ g`, for an
exact functor `g`: the counit of `L(f)` followed by the identification of `D(g)` with `g`
applied levelwise. This is `Functor.leftDerivedFunctorCompMapDerivedCategoryRightCounit`
without the associators. -/
noncomputable def leftDerivedFunctorCompExactCounit :
    DerivedCategory.Qh ⋙ L(f) ⋙ D(g) ⟶ (f ⋙ g).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight f.leftDerivedFunctorCounit D(g) ≫
    Functor.whiskerLeft (f.mapHomotopyCategory (.up ℤ)) g.mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (f ⋙ g)) (.up ℤ)).hom
      DerivedCategory.Qh

lemma leftDerivedFunctorCompExactCounit_app
    (K : HomotopyCategory C (.up ℤ)) :
    (leftDerivedFunctorCompExactCounit f g).app K =
      D(g).map (f.leftDerivedFunctorCounit.app K) ≫
        g.mapDerivedCategoryFactorsh.hom.app ((f.mapHomotopyCategory (.up ℤ)).obj K) := by
  simp [leftDerivedFunctorCompExactCounit,
    Functor.mapHomotopyCategoryCompIso_refl_hom_app]

/-- `L(f) ⋙ D(g)`, with the counit `Functor.leftDerivedFunctorCompExactCounit`, is a left derived
functor of `f ⋙ g`. -/
lemma isLeftDerivedFunctor_leftDerivedFunctorCompExactCounit :
    (L(f) ⋙ D(g)).IsLeftDerivedFunctor (leftDerivedFunctorCompExactCounit f g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  have := preservesKFlatQuasiIso_comp_of_exact f g
  rw [Functor.isLeftDerivedFunctor_iff_isIso_app_of_kFlat]
  intro K hK
  have := f.isIso_leftDerivedFunctorCounit_app_of_kFlat K hK
  rw [leftDerivedFunctorCompExactCounit_app]
  infer_instance

end LeftDerivedCompMapDerivedCategory

end CategoryTheory.Functor
