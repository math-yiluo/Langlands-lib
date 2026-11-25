/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarConstantPullback

/-! # A shared canonical scalar coefficient isomorphism -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local instance 2000] CategoryTheory.instAdditiveSheafConstantSheaf

/-- The canonical scalar coefficient is identified with the derived constant
single complex by scalar restriction and the exact constant/single comparison.
Source: Mathlib `constantCommuteCompose` and `mapDerivedCategorySingleFunctor`.
(blueprint: def-pur-etale-scalar-constant-coefficient-iso) -/
def etaleScalarConstantCoefficientIso
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    (W : Scheme.{u}) : scalarCoefficient a W ≅
      (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
          ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))) :=
  (DerivedCategory.singleFunctor _ 0).mapIso
      ((constantCommuteCompose W.smallEtaleTopology
        (ModuleCat.restrictScalars a)).app (ModuleCat.of D D)) ≪≫
    (Functor.mapDerivedCategorySingleFunctor
      (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).symm.app
        ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))

private theorem coefficientIso_eq
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    (W : Scheme.{u}) : etaleScalarConstantCoefficientIso a W =
      (DerivedCategory.singleFunctor _ 0).mapIso
        ((constantCommuteCompose W.smallEtaleTopology
          (ModuleCat.restrictScalars a)).app (ModuleCat.of D D)) ≪≫
      (Functor.mapDerivedCategorySingleFunctor
        (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).symm.app
          ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D)) := by
  rfl

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory Functor.rightDerivedFunctor
  derivedTensor upperStar lowerStar HasDerivedCategory.standard
  Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategorySingleFunctor singleFunctorCompLeftDerivedUpperStarIso
  exceptionalConstantPullbackIso scalarCoefficientPullbackIso

/-- The specified scalar coefficient identification commutes with inverse image.
Source: Stacks Tags 03EK and 07A6; Zheng Construction 2.26.
(blueprint: lem-pur-etale-scalar-constant-coefficient-iso-pullback)

Proof: expand the canonical coefficient identification and apply the scalar
constant pullback square, which was proved by the ordinary unit calculation
and the exact derivation/single comparison. -/
theorem etaleScalarConstantCoefficientIso_pullback
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} C) f).leftDerivedFunctor.map
        (etaleScalarConstantCoefficientIso a Y).hom ≫
      (exceptionalConstantPullbackIso C f).hom.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
          ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))) =
      (scalarCoefficientPullbackIso a f).hom ≫ (etaleScalarConstantCoefficientIso a X).hom := by
  simp only [coefficientIso_eq]
  exact etaleScalarConstantPullback a f

end AlgebraicGeometry.Etale
