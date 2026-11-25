/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatNat

/-!
# `H⁰` of a total right derived functor on objects in degree zero

For a left exact additive functor `F : C ⥤ D` between abelian categories, where `C` has enough
injectives and K-injective resolutions, the zeroth cohomology of the unbounded total right
derived functor `RF` applied to an object placed in degree `0` is `F` itself, naturally:
`H⁰(RF(X[0])) ≅ F X`
(`CategoryTheory.Functor.singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso`).
It is the composite of `H⁰(RF(X[0])) ≅ R⁰F X`
(`CategoryTheory.Functor.homologyRightDerivedFunctorObjSingleFunctorIso`) with
`R⁰F ≅ F` (`CategoryTheory.Functor.rightDerivedZeroIsoSelf`).
-/

@[expose] public section

open CategoryTheory Abelian Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [EnoughInjectives C]
  [HasKInjectiveResolutions C]

/-- For a left exact functor `F`, the zeroth cohomology of the total right derived functor `RF`
on objects placed in degree `0` is `F`: `H⁰(RF(X[0])) ≅ R⁰F X ≅ F X`, naturally in `X`. -/
noncomputable def singleFunctorCompRightDerivedFunctorCompHomologyFunctorZeroIso :
    DerivedCategory.singleFunctor C 0 ⋙ F.rightDerivedFunctor ⋙
        DerivedCategory.homologyFunctor D 0 ≅ F :=
  NatIso.ofComponents
    (fun X ↦ F.homologyRightDerivedFunctorObjSingleFunctorIso X 0 ≪≫
      F.rightDerivedZeroIsoSelf.app X)
    fun {X Y} f ↦ by
      have h := F.homologyRightDerivedFunctorObjSingleFunctorIso_hom_naturality f 0
      simp only [Functor.comp_map, Iso.trans_hom, Iso.app_hom, Category.assoc]
      erw [reassoc_of% h]
      rw [F.rightDerivedZeroIsoSelf.hom.naturality]

end CategoryTheory.Functor
