/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteBoundaryEquation

/-! # Normalized finite coordinates for the supported Cartier calculation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  CategoryTheory.Abelian.Ext HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalFiniteToPadic diagonalForget SpTowerClasses.lineModule
  comparisonUpperStar cartierProRootMap

/-- Coordinates on the evaluated coefficient unit and line, fixed on one and roots.
The coefficient normalization is imposed on every local section corresponding to
one under the specified coefficient comparison. The line normalization is the
actual root tensor map, not an unspecified line isomorphism.
Source: diagonal trace proof (2), finite coefficient and root identifications.
(blueprint: def-sfb-diagonal-trace-supported-finite-boundary-frame). -/
structure SupportedFiniteBoundaryFrame
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r) (n : ℕ) where
  coefficient :
    (r.F.obj (SpTowerClasses.coefficient (diagonalSurface Y)
      (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))).obj (op n) ≅
    (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
      (geoCartierConstant (diagonalResidue.{u} l n) (diagonalSurface Y))
  line : (r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c)).obj (op n) ≅
    (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
      (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y))
  coefficient_one : ∀ (U : (diagonalSurface Y).ProEtᵒᵖ)
      (x : ((r.F.obj (SpTowerClasses.coefficient (diagonalSurface Y)
        (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))).obj
          (op n)).obj.obj U),
    HEq x (1 : (SpTowerClasses.systemRing l (ULift.{u} (Padic l))
      (diagonalSurface Y)).obj.obj (op (n, U.unop))) →
    HEq (coefficient.hom.hom.app U x)
      ((toSheafify (Scheme.ProEt.topology (diagonalSurface Y))
        ((Functor.const (diagonalSurface Y).ProEtᵒᵖ).obj
          (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n)))).app U
            (1 : diagonalResidue.{u} l n))
  line_roots : HEq ((diagonalForget l (diagonalSurface Y)).map line.hom)
    (k.lineForget.hom.app (op n) ≫
      cartierProRootMap (diagonalResidue.{u} l n) (l ^ (n + 1))
        (cartierResidue_cast l (n + 1)) (diagonalSurface Y)
        (pow_pos (Fact.out : l.Prime).pos _) (diagonalSurface_power_unit l Y hY n))

/-- Evaluate an exact image of a single sheaf, using only the canonical comparisons.
Source: exact evaluation and exact restriction comparisons.
(blueprint: def-sfb-diagonal-trace-supported-finite-boundary-unit-coordinates). -/
@[irreducible] def supportedFiniteSingleCoordinates
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ (ℕᵒᵖ ⥤ B)) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : A) (n : ℕ) {P : B} (a : (F.obj M).obj (op n) ≅ P) :
    (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).obj
      (F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj M)) ≅
        (DerivedCategory.singleFunctor B 0).obj P :=
  (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).mapIso
      ((F.mapDerivedCategorySingleFunctor 0).app M) ≪≫
    (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor B 0).mapIso a

/-- The analogous coordinates after shifting by two, with both exact shift maps.
Source: exact shift comparisons in the finite Cartier calculation.
(blueprint: def-sfb-diagonal-trace-supported-finite-boundary-line-coordinates). -/
@[irreducible] def supportedFiniteShiftedCoordinates
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory (ℕᵒᵖ ⥤ B)]
    (F : A ⥤ (ℕᵒᵖ ⥤ B)) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : A) (n : ℕ) {P : B} (a : (F.obj M).obj (op n) ≅ P) :
    (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).obj
      (F.mapDerivedCategory.obj
        (((DerivedCategory.singleFunctor A 0).obj M)⟦(2 : ℤ)⟧)) ≅
        ((DerivedCategory.singleFunctor B 0).obj P)⟦(2 : ℤ)⟧ :=
  (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).mapIso
      ((F.mapDerivedCategory.commShiftIso (2 : ℤ)).app _) ≪≫
    ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso (supportedFiniteSingleCoordinates F M n a)

/-- Forget support of a finite Cartier class and express its arrow in the fixed
coefficient coordinates. The input is the actual coefficient cone projection;
no arbitrary intermediate morphism or witness of an existence theorem is used.
Source: diagonal trace proof (2), the constant-to-supported finite Cartier arrow.
(blueprint: def-sfb-diagonal-trace-supported-finite-boundary-cartier-map). -/
@[irreducible] def SupportedFiniteBoundaryFrame.cartierMap
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y)))
    (z : GeoCartierClass (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalImmersion Y)) :
    (diagonalCompletedUnderlying l (diagonalSurface Y)).obj
      (completedUnit l (diagonalSurface Y)) ⟶
    (((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
      (op n)).mapDerivedCategory).obj
      (r.F.mapDerivedCategory.obj
        ((SpTowerClasses.line l (ULift.{u} (Padic l)) c)⟦(2 : ℤ)⟧)) :=
  (k.unitMap l (ULift.{u} (Padic l)) L ≫ (L.projection n).app _) ≫
    (supportedFiniteSingleCoordinates r.F _ n a.coefficient).hom ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((diagonalFiniteToPadic l n (diagonalSurface Y)).map
        (Scheme.proEtaleConstantDirectImageMap (diagonalImmersion Y)
          (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
          (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n)))) ≫
    (diagonalExactFunctorExtImage (diagonalFiniteToPadic l n (diagonalSurface Y)) z).hom ≫
    (supportedFiniteShiftedCoordinates r.F _ n a.line).inv

end AlgebraicGeometry.ProEtale.DiagonalTrace
