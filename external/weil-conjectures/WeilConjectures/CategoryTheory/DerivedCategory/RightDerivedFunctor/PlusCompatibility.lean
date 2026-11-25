/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle

/-!
# Compatibility of the unbounded right derived functor with `rightDerivedFunctorPlus`

Let `F : C ⥤ D` be an additive functor between abelian categories, where `C` has
enough injectives and K-injective resolutions. This file identifies the restriction
of the unbounded total right derived functor
`F.rightDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D` to the bounded below
derived category with the right derived functor
`F.rightDerivedFunctorPlus : DerivedCategory.Plus C ⥤ DerivedCategory.Plus D`:

`F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
  DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor`

(`Functor.rightDerivedFunctorPlusCompatibility`). In particular the homology of the unbounded
total right derived functor applied to an object placed in degree `0` is given by the
classical right derived functors, `H^n(RF(X[0])) ≅ RⁿF X`
(`Functor.homologyRightDerivedFunctorObjSingleFunctorIso`), and it vanishes in negative
degrees (`Functor.isGE_rightDerivedFunctor_obj_singleFunctor`).
-/

@[expose] public section

open CategoryTheory Abelian Limits

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [EnoughInjectives C] [HasKInjectiveResolutions C]

/-- The unit exhibiting `F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι` as a right
derived functor of `F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
DerivedCategory.Plus.ι`, obtained by whiskering `F.rightDerivedFunctorPlusUnith` with the
inclusion of the bounded below derived category. -/
noncomputable def rightDerivedFunctorPlusιUnit :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι :=
  Functor.whiskerRight F.rightDerivedFunctorPlusUnith DerivedCategory.Plus.ι

instance : (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).IsRightDerivedFunctor
    F.rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C) :=
  (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso _
    (fun X₁ ↦ inferInstanceAs (IsIso (DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlusUnith.app
        ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X₁)))))

/-- The unit exhibiting `DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor` as a right
derived functor of `F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙
DerivedCategory.Plus.ι`, obtained by whiskering `F.rightDerivedFunctorUnit` with the
inclusion of the bounded below homotopy category. -/
noncomputable def ιRightDerivedFunctorUnit :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor :=
  Functor.whiskerLeft (HomotopyCategory.Plus.ι C) F.rightDerivedFunctorUnit

instance : (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor).IsRightDerivedFunctor
    F.ιRightDerivedFunctorUnit (HomotopyCategory.Plus.quasiIso C) :=
  (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso _
    (fun X₁ ↦ by
      obtain ⟨X₁, hX₁⟩ := X₁
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X₁
      obtain ⟨n, _⟩ := (HomotopyCategory.plus_quotient_obj_iff _).mp hX₁
      have hinj : ∀ (i : ℤ), Injective
          ((((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X i) :=
        fun i ↦ inferInstanceAs (Injective ((InjectiveObject.ι C).obj (K.X i)))
      have : CochainComplex.IsKInjective
          (((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
        CochainComplex.isKInjective_of_injective _ n
      exact inferInstanceAs (IsIso (F.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          (((InjectiveObject.ι C).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)))))

/-- The restriction of the unbounded total right derived functor
`F.rightDerivedFunctor : DerivedCategory C ⥤ DerivedCategory D` to the bounded below
derived category identifies with the right derived functor
`F.rightDerivedFunctorPlus` on the bounded below derived categories. -/
noncomputable def rightDerivedFunctorPlusCompatibility :
    F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor :=
  Functor.rightDerivedUnique _ _ F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
    (HomotopyCategory.Plus.quasiIso C)

/-- The `n`-th homology of the unbounded total right derived functor `RF` applied to `X`
placed in degree `0` is the classical right derived functor `RⁿF X`. -/
noncomputable def homologyRightDerivedFunctorObjSingleFunctorIso (X : C) (n : ℕ) :
    (DerivedCategory.homologyFunctor D n).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X)) ≅
      (F.rightDerived n).obj X :=
  (DerivedCategory.homologyFunctor D n).mapIso
      (F.rightDerivedFunctorPlusCompatibility.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X)).symm ≪≫
    F.homologyRightDerivedFunctorPlusObjSingleFunctorIso X n

/-- The unbounded total right derived functor `RF` of an object `X` placed in degree `0` is
concentrated in degrees `≥ 0`: it is computed by `F` applied to an injective resolution of
`X`. -/
lemma isGE_rightDerivedFunctor_obj_singleFunctor (X : C) :
    (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj X)).IsGE 0 := by
  have : (F.rightDerivedPlusComplex X).obj.IsStrictlyGE 0 := by
    dsimp [rightDerivedPlusComplex]
    infer_instance
  refine (DerivedCategory.isGE_iff _ 0).2 fun i hi ↦ ?_
  exact (((F.rightDerivedPlusComplex X).obj.exactAt_of_isGE 0 i hi).isZero_homology).of_iso
    ((DerivedCategory.homologyFunctor D i).mapIso
        (F.rightDerivedFunctorPlusCompatibility.app
          ((DerivedCategory.Plus.singleFunctor C 0).obj X)).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor D i).mapIso
        (F.rightDerivedFunctorPlusObjSingleFunctorIsoQ X) ≪≫
      DerivedCategory.Plus.homologyFunctorObjQIso _ i)

end Functor

end CategoryTheory
