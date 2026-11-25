/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteRealizedClassCore

/-! # The derived representative of a finite realization

Source: diagonal tower coefficient changes (1), scalar compatibility and Ext realization.
(blueprint: lem-diagonal-finite-realized-class-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

attribute [local irreducible] geoCartierConstant geoCartierLine
  quotientLine quotientLineMap cyclicLine cyclicLineMap
  derivedScalars QuotientLineRealization CyclicCartierFrame.reduce
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor Endpoint.shift
  Mod.extendScalars AlgebraicGeometry.ProEtale.upperStarFromPoint
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  DerivedCategory.singleFunctorIsoCompQ
  HasDerivedCategory.standard DerivedCategory.singleFunctors HomotopyCategory.singleFunctors

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The finite realization represents its explicitly supplied derived arrow. -/
theorem finiteRealizedClass_hom
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {A : Type (u + 1)} [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (Y : Scheme.{u})
    {L : ∀ X : Scheme.{u}, Modules R X}
    (eW : FiniteRealization R A (diagonalSurface Y))
    (line : eW.F.obj (L (diagonalSurface Y)) ≅ geoCartierLine A N hA (diagonalSurface Y))
    (s : eW.F.obj (source R Y) ≅
      (lowerStar (ModuleCat.{u + 1} A) (diagonalImmersion Y)).obj
        (geoCartierConstant A (ProjectiveLine Y)))
    (α : (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj
      (source R Y) ⟶
      ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj
        (L (diagonalSurface Y)))⟦(2 : ℤ)⟧) :
    (finiteRealizedClass N hA Y eW line s α).hom =
      ((DerivedCategory.singleFunctor _ 0).map s.inv ≫
        SpTowerClasses.mapSingleArrow eW.F (X := source R Y)
          (Y := L (diagonalSurface Y)) (2 : ℤ) α ≫
          ((DerivedCategory.singleFunctor _ 0).map line.hom)⟦(2 : ℤ)⟧') := by
  rw [finiteRealizedClass_eq_arrowClass]
  exact finiteArrowClass_hom _

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
