/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarSheafTensorPullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison

/-!
# The tensor comparison with a coefficient sheaf in degree zero

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0FPH
(blueprint: def-pur-upper-star-single-tensor-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar lowerStar

/-- The canonical localization comparison for tensoring with a sheaf in degree zero.
Source: Stacks 0G7E (blueprint: def-pur-upper-star-single-tensor-comparisons). -/
def tensorSingleRepresentative
    {C : Type w} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]
    (M : C) (P : CochainComplex C ℤ) :
    (scalarTensorModelFunctor M).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P) :=
  Functor.LaxMonoidal.μ DerivedCategory.Q P
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
    DerivedCategory.Q.map
      ((CochainComplex.map₂HomologicalComplexFlipObjSingleIso
        (curriedTensor _) M).hom.app P)

/-- Exact pullback on a sheaf in degree zero followed by a specified coefficient iso.
Source: Stacks 07A4 (blueprint: def-pur-upper-star-single-tensor-comparisons). -/
def upperStarSingleCoefficientIso
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    {M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (k : (upperStar (ModuleCat.{u + 1} A) f).obj M ≅ N) :
    L(upperStar (ModuleCat.{u + 1} A) f).obj
        ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj N :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).app _ ≪≫
    ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategorySingleFunctor 0).app M ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso k

/-- Ordinary pullback commutes with tensoring by a sheaf, including a coefficient iso.
Source: Stacks 07A4 (blueprint: def-pur-upper-star-single-tensor-comparisons). -/
def upperStarTensorSingleIso
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    {M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (k : (upperStar (ModuleCat.{u + 1} A) f).obj M ≅ N) :
    tensorRight M ⋙ upperStar (ModuleCat.{u + 1} A) f ≅
      upperStar (ModuleCat.{u + 1} A) f ⋙ tensorRight N :=
  NatIso.ofComponents
    (fun X ↦ asIso (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f) X M) ≪≫
      (tensorLeft _).mapIso k)
    (by
      intro X Y a
      change (upperStar (ModuleCat.{u + 1} A) f).map (a ▷ M) ≫
          Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f) Y M ≫
          ((upperStar (ModuleCat.{u + 1} A) f).obj Y ◁ k.hom) =
        (Functor.OplaxMonoidal.δ (upperStar (ModuleCat.{u + 1} A) f) X M ≫
          ((upperStar (ModuleCat.{u + 1} A) f).obj X ◁ k.hom)) ≫
          ((upperStar (ModuleCat.{u + 1} A) f).map a ▷ N)
      rw [← Functor.OplaxMonoidal.δ_natural_left_assoc, Category.assoc]
      exact congrArg (fun z ↦ Functor.OplaxMonoidal.δ
        (upperStar (ModuleCat.{u + 1} A) f) X M ≫ z)
        (whisker_exchange _ _).symm)

end AlgebraicGeometry.Etale
