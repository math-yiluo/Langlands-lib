/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Bounded below right derived functors: composition with arbitrary functors, exact functors

Two complements to Mathlib's `CategoryTheory.Functor.rightDerivedFunctorPlus`, the bounded
below right derived functor `R⁺F : D⁺(C) ⥤ D⁺(D)` of an additive functor `F : C ⥤ D` between
abelian categories with `C` having enough injectives.

- `CategoryTheory.Functor.isRightDerivedFunctor_rightDerivedFunctorPlus_comp_right`: for
  *any* functor `G : D⁺(D) ⥤ E`, the composite `R⁺F ⋙ G` is a right derived functor of
  `F.mapHomotopyCategoryPlus ⋙ Qh ⋙ G`, with unit the unit of `R⁺F` whiskered by `G`. This
  is the "absoluteness" of the bounded below right derived functor: the unit of `R⁺F` is an
  isomorphism on bounded below complexes of injectives, which is all that the injective
  derivability structure asks for (`HomotopyCategory.Plus.localizerMorphism_derives`).
- `CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit`: if `F` is exact, the unit
  `F.mapHomotopyCategoryPlus ⋙ Qh ⟶ Qh ⋙ R⁺F` is an isomorphism: the right derived functor
  is computed by applying `F` levelwise, with no resolution needed. Consequently `R⁺F` is
  canonically isomorphic to `F.mapDerivedCategoryPlus`
  (`CategoryTheory.Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus`), the bounded
  below counterpart of `CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Category Limits Abelian

namespace CategoryTheory.Functor

section Comp

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} [Category.{v₁} C] [Category.{v₂} D]
  [Category.{v₃} E] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives C] (F : C ⥤ D) [F.Additive] (G : DerivedCategory.Plus D ⥤ E)

/-- The composite of the bounded below right derived functor of `F` with an arbitrary
functor `G` out of the bounded below derived category is a right derived functor of
`F.mapHomotopyCategoryPlus ⋙ Qh ⋙ G`, with the evident unit: the unit of `R⁺F` is an
isomorphism on bounded below complexes of injectives, which is all that
`HomotopyCategory.Plus.localizerMorphism_derives` asks for. -/
instance isRightDerivedFunctor_rightDerivedFunctorPlus_comp_right :
    (F.rightDerivedFunctorPlus ⋙ G).IsRightDerivedFunctor
      (Functor.whiskerRight F.rightDerivedFunctorPlusUnith G ≫ (Functor.associator _ _ _).hom)
      (HomotopyCategory.Plus.quasiIso C) := by
  refine (HomotopyCategory.Plus.localizerMorphism_derives
    ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ G)).isRightDerivedFunctor_of_isIso _
    (fun X₁ => ?_)
  have : IsIso (F.rightDerivedFunctorPlusUnith.app
    ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X₁)) := inferInstance
  dsimp
  infer_instance

end Comp

section Exact

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives C] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F]

/-- The functor `F.mapDerivedCategoryPlus` induced by an exact functor `F` on the bounded
below derived categories is a right derived functor of `F.mapHomotopyCategoryPlus ⋙ Qh`,
with unit the inverse of the comparison `F.mapDerivedCategoryPlusFactorsh`: the unit is an
isomorphism, and `Qh` is a localization functor for quasi-isomorphisms. -/
instance isRightDerivedFunctor_mapDerivedCategoryPlus :
    F.mapDerivedCategoryPlus.IsRightDerivedFunctor F.mapDerivedCategoryPlusFactorsh.inv
      (HomotopyCategory.Plus.quasiIso C) :=
  isRightDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryPlusFactorsh

/-- For an *exact* functor `F` between abelian categories, the bounded below right derived
functor is canonically isomorphic to the functor `F.mapDerivedCategoryPlus` induced by
applying `F` levelwise: both are right derived functors of `F.mapHomotopyCategoryPlus ⋙ Qh`,
and right derived functors are unique up to canonical isomorphism. -/
noncomputable def rightDerivedFunctorPlusIsoMapDerivedCategoryPlus :
    F.rightDerivedFunctorPlus ≅ F.mapDerivedCategoryPlus :=
  rightDerivedUnique F.rightDerivedFunctorPlus F.mapDerivedCategoryPlus
    F.rightDerivedFunctorPlusUnith F.mapDerivedCategoryPlusFactorsh.inv
    (HomotopyCategory.Plus.quasiIso C)

@[reassoc (attr := simp)]
lemma rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac :
    F.rightDerivedFunctorPlusUnith ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh
          F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom =
      F.mapDerivedCategoryPlusFactorsh.inv := by
  simp [rightDerivedFunctorPlusIsoMapDerivedCategoryPlus]

/-- The unit of the bounded below right derived functor of an *exact* functor is an
isomorphism everywhere: the right derived functor is computed by applying the functor
levelwise, with no resolution needed. -/
instance isIso_rightDerivedFunctorPlusUnit : IsIso F.rightDerivedFunctorPlusUnith := by
  have : IsIso (F.rightDerivedFunctorPlusUnith ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh
        F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom) := by
    rw [F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (Functor.whiskerLeft DerivedCategory.Plus.Qh
      F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom)

end Exact

end CategoryTheory.Functor
