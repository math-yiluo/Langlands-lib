/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients

/-! # Exact transport of the strict root system to the coefficient Tate line -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace

attribute [local instance] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory

/-- Transport a shifted strict root system to the restricted coefficient Tate line.
This uses the specified root-system isomorphism, the exact single comparison,
and the exact restriction functor's shift comparison, in that order.
Source: diagonal tower trace proof (1), identification of the finite root systems.
(blueprint: def-sfb-diagonal-trace-root-system-transport). -/
@[irreducible]
def rootSystemTransport
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (N : A) {H : B} {J : DerivedCategory B}
    (b : J ≅ ((DerivedCategory.singleFunctor B 0).obj H)⟦(2 : ℤ)⟧)
    (e : H ≅ F.obj N) :
    J ≅ F.mapDerivedCategory.obj
      (((DerivedCategory.singleFunctor A 0).obj N)⟦(2 : ℤ)⟧) :=
  b ≪≫ (shiftFunctor _ (2 : ℤ)).mapIso
    ((DerivedCategory.singleFunctor B 0).mapIso e) ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (((F.mapDerivedCategorySingleFunctor 0).app N).symm) ≪≫
    ((F.mapDerivedCategory.commShiftIso (2 : ℤ)).app
      ((DerivedCategory.singleFunctor A 0).obj N)).symm

/-- The exact root transport with the published coefficient Tate-line endpoint.
Its endpoint is the existing line object, so later statements share that object
without repeatedly identifying its unfolded single-complex presentation.
Source: diagonal trace proof (1), strict root-system identification.
(blueprint: def-sfb-diagonal-trace-coefficient-root-transport). -/
@[irreducible]
def coefficientRootTransport (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    [DiagonalTraceLocalizations l T]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) T)
    (r : Restriction l (ULift.{u} (Padic l)) T)
    {H : DiagonalSystems l T} {J : DerivedCategory (DiagonalSystems l T)}
    (b : J ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (e : H ≅ r.F.obj (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c)) :
    J ≅ r.F.mapDerivedCategory.obj ((SpTowerClasses.line l (ULift.{u} (Padic l)) c)⟦(2 : ℤ)⟧) :=
  rootSystemTransport r.F (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c) b e

end AlgebraicGeometry.ProEtale.DiagonalTrace
