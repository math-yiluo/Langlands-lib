/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierClass
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteRootNormalization
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit

/-! # The positive finite Cartier-cycle normalization -/

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
  diagonalCompletedSource diagonalCompletedCoefficientMap

attribute [local irreducible] CategoryTheory.Abelian.Ext
  HasDerivedCategory.standard HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization
  comparisonUpperStar cartierUnitsComparison cartierRootsComparison
  cartierRootsIso cartierEtaleKummerUnit cartierProKummerUnit cartierReducedEtale
  cartierReducedPro CartierEtaleReductionSpec CartierProReductionSpec
  cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  diagonalSingleLimitComparison diagonalExactFunctorExtImage
  diagonalShiftedSingleLimitComparison diagonalCompletedGenerator

/-- The positive finite Cartier-cycle normalization, named with its scalar endpoints.
This is exactly the finite-cycle clause of IsDiagonalLimit, for an ordinary
reduction presentation and a specified strict Ext class.
Source: diagonal-limit clause (3), positive finite Cartier reductions.
(blueprint: def-sfb-diagonal-trace-finite-cartier-normalization). -/
@[irreducible]
def FiniteCartierNormalization
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    [HasExt.{u + 1} (DiagonalSystems l (diagonalSurface Y))]
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (xi : Ext (D.E.obj (diagonalIntegralSource Y)) H 2)
    : Prop :=
  diagonalFiniteCycleNormalization
      (A := DiagonalMod l (diagonalSurface Y))
      (D.E.obj (diagonalIntegralSource Y)) H xi
      (fun n ↦ (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
          (diagonalImmersion Y)).obj
            (geoCartierConstant (diagonalResidue.{u} l n) (ProjectiveLine Y))))
      (fun n ↦ (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
        (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
          (cartierResidue_cast l (n + 1)) (diagonalSurface Y)))
      (fun n s ↦ DiagonalSourceNormalization l Y D n s)
      (FiniteRootNormalization l Y hY H roots)
      (finiteCartierClass l Y hY)

end AlgebraicGeometry.ProEtale.DiagonalTrace
