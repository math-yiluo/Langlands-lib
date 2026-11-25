/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# The unbounded derived adjunction of an adjunction with exact left adjoint

Let `L ⊣ R` be an adjunction of additive functors between abelian categories, with `L`
exact and the target of `L` having K-injective resolutions. Then the functor
`L.mapDerivedCategory` induced by `L` on the unbounded derived categories is left adjoint to
the total right derived functor `R.rightDerivedFunctor`.

This is the unbounded counterpart of `CategoryTheory.Adjunction.derivedPlus`. Unlike
`CategoryTheory.Adjunction.derivedAdjunction`, the left adjoint is not derived: `L` being
exact, no K-flat resolutions and hence no monoidal structure on the source are involved.

## Main definitions

- `CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`: the adjunction
  `L.mapDerivedCategory ⊣ R.rightDerivedFunctor`.

## The proof

As for `CategoryTheory.Adjunction.derivedPlus`, the construction is Mathlib's
`CategoryTheory.Adjunction.derived` applied to the adjunction
`L.mapHomotopyCategory (.up ℤ) ⊣ R.mapHomotopyCategory (.up ℤ)`, and there are two
absoluteness statements to check:

* `L.mapDerivedCategory ⋙ R.rightDerivedFunctor` is a left derived functor because the
  comparison map is an isomorphism, `L` being exact;
* `R.rightDerivedFunctor ⋙ L.mapDerivedCategory` is a right derived functor by the
  K-injective right derivability structure, since the unit of `R.rightDerivedFunctor` is an
  isomorphism on K-injective complexes.

-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Limits Abelian

namespace CategoryTheory.Adjunction

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

instance isLeftDerivedFunctor_mapDerivedCategory :
    L.mapDerivedCategory.IsLeftDerivedFunctor L.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ L.mapDerivedCategoryFactorsh

instance isLeftDerivedFunctor_mapDerivedCategory_comp_rightDerivedFunctor :
    (L.mapDerivedCategory ⋙ R.rightDerivedFunctor).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctor)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight L.mapDerivedCategoryFactorsh R.rightDerivedFunctor)

instance isRightDerivedFunctor_rightDerivedFunctor_comp_mapDerivedCategory :
    (R.rightDerivedFunctor ⋙ L.mapDerivedCategory).IsRightDerivedFunctor
      (Functor.whiskerRight R.rightDerivedFunctorUnit L.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso D (ComplexShape.up ℤ)) :=
  (HomotopyCategory.KInjectives.localizerMorphism D)
    |>.isRightDerivedFunctor_comp_of_isRightDerivabilityStructure _
      (fun I ↦ (HomotopyCategory.KInjectives.localizerMorphism_derives
        _).isIso_of_isRightDerivedFunctor _ I) _

/-- The unbounded derived adjunction of an adjunction `adj : L ⊣ R` of additive functors
between abelian categories with `L` exact: the functor `L.mapDerivedCategory` induced by `L`
on the unbounded derived categories is left adjoint to the total right derived functor
`R.rightDerivedFunctor` of `R`. -/
noncomputable def mapDerivedCategoryRightDerivedAdjunction (adj : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.rightDerivedFunctor :=
  (adj.mapHomotopyCategory (ComplexShape.up ℤ)).derived
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso D (ComplexShape.up ℤ))
    L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit

end CategoryTheory.Adjunction
