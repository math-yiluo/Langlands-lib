/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicCartierFrame
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicFunctorCalculus

/-! # Finite scalar evaluation functor and its endpoints

Source: diagonal tower coefficient changes (1), and limit (3).
(blueprint: def-diagonal-cyclic-finite-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 5000] cyclicSmallShiftedSingleHom

attribute [local irreducible] CategoryTheory.Abelian.Ext Ext.homEquiv
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HomotopyCategory.singleFunctors DerivedCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ Functor.mapDerivedCategory shiftFunctor
  diagonalFiniteToPadic cyclicLine cyclicLineMap derivedScalars
  geoCartierConstant geoCartierLine

/-- Explicit finite evaluation functor or endpoint composite.
Source: coefficient changes (1), scalar quotient and finite realization.
(blueprint: def-diagonal-cyclic-finite-evaluation). -/
def cyclicFiniteEvaluationFunctor
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (p : CyclicCartierFrame l Y n) :
    DerivedCategory (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l])
      (diagonalSurface Y)) ⥤ DerivedCategory (DiagonalMod l (diagonalSurface Y)) :=
  derivedScalars (cyclicMap l n) (diagonalSurface Y) ⋙ p.eW.F.mapDerivedCategory ⋙
    (diagonalFiniteToPadic l n (diagonalSurface Y)).mapDerivedCategory

/-- Explicit finite evaluation functor or endpoint composite.
Source: coefficient changes (1), scalar quotient and finite realization.
(blueprint: def-diagonal-cyclic-finite-evaluation). -/
def cyclicFiniteEvaluationSource
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (p : CyclicCartierFrame l Y n) :
    (DerivedCategory.singleFunctor (DiagonalMod l (diagonalSurface Y)) 0).obj
        ((diagonalFiniteToPadic l n (diagonalSurface Y)).obj
          ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
            (diagonalImmersion Y)).obj
              (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y)))) ⟶
      (cyclicFiniteEvaluationFunctor l Y n p).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)) :=
  threeFunctorSource (derivedScalars (cyclicMap l n) (diagonalSurface Y))
    p.eW.F (diagonalFiniteToPadic l n (diagonalSurface Y))
    p.supported.iso.inv p.sourceComparison.iso

/-- Explicit finite evaluation functor or endpoint composite.
Source: coefficient changes (1), scalar quotient and finite realization.
(blueprint: def-diagonal-cyclic-finite-evaluation). -/
def cyclicFiniteEvaluationTarget
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (n : ℕ)
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (p : CyclicCartierFrame l Y n) :
    (cyclicFiniteEvaluationFunctor l Y n p).obj
        (((DerivedCategory.singleFunctor _ 0).obj
          (zlLine l (diagonalSurface Y)))⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor (DiagonalMod l (diagonalSurface Y)) 0).obj
        ((diagonalFiniteToPadic l n (diagonalSurface Y)).obj
          (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
            (cartierResidue_cast l (n + 1)) (diagonalSurface Y))))⟦(2 : ℤ)⟧ :=
  threeFunctorTarget (derivedScalars (cyclicMap l n) (diagonalSurface Y))
    p.eW.F (diagonalFiniteToPadic l n (diagonalSurface Y)) 2
    (p.line.shift (cyclicMap l n)) p.lineEndpoint.iso

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
