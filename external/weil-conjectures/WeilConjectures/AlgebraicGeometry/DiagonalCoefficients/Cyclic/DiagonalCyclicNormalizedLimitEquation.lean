/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicQuotientFunctors
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Supported.DiagonalTraceSupportedSourceConeNormalization

/-! # Supplied normalized diagonal limit data

Source: diagonal limit (3).
(blueprint: def-diagonal-cyclic-normalized-limit-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local semireducible] cyclicCompletedQuotient cyclicDiscreteRestriction
  cyclicSystemEvaluation

attribute [local irreducible] diagonalSourceLimitMap diagonalTargetLimitMap

attribute [local instance 4000] AlgebraicGeometry.ProEtale.diagonalHasLimit
  AlgebraicGeometry.ProEtale.diagonalModLimits

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  diagonalCompletedSource diagonalCompletedCoefficientMap
  CategoryTheory.Abelian.Ext HasDerivedCategory.standard
  HasDerivedCategory.ofIsGrothendieckAbelian HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctors DerivedCategory.singleFunctorIsoCompQ
  diagonalDerivedSingleCounit DiagonalSourceNormalization comparisonUpperStar
  cartierUnitsComparison cartierRootsComparison cartierRootsIso cartierEtaleKummerUnit
  cartierProKummerUnit cartierReducedEtale cartierReducedPro CartierEtaleReductionSpec
  CartierProReductionSpec cartierProIntegralGenerator cartierProRootMap cartierResidueReducedPro
  diagonalFiniteToPadic diagonalForget diagonalScalarExtension diagonalScalarAdjunction
  diagonalIntegralBoundary diagonalSingleLimitComparison
  diagonalShiftedSingleLimitComparison diagonalCompletedGenerator

/-- Normalized coefficient cones and their whole-limit equation, with supplied objects.
Source: diagonal limit (3) (blueprint: def-diagonal-cyclic-normalized-limit-equation).
No witness is selected by this predicate. -/
@[irreducible] def cyclicNormalizedLimitEquation (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    [dAb : HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [dMod : HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [dSys : HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [dComp : HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [dCompSys : HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y)
    (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
      (M : DiagonalCompletedReduction ℓ (diagonalSurface Y))
      (s₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (diagonalCompletedSource ℓ Y) ≅
        limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
      (t₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H) : Prop :=
  let R := cyclicDiscreteRestriction ℓ (diagonalSurface Y)
  let source := diagonalSourceLimitMap ℓ Y D a L s₀
  let target := diagonalTargetLimitMap ℓ Y D H b L t₀
  (DiagonalTrace.SupportedSourceConeNormalization ℓ Y D.ordinary s₀ ∧
  HEq ((diagonalForget ℓ (diagonalSurface Y)).map t₀.hom)
    (diagonalRootLimitComparison ℓ (diagonalSurface Y) H roots).inv ∧
  DiagonalArrowCompatibility ℓ R L.R
    (cyclicCompletedQuotient ℓ (diagonalSurface Y) M)
    (cyclicSystemEvaluation ℓ (diagonalSurface Y))
    M.unit L.projection (diagonalCompletedDomain ℓ Y) (diagonalCompletedCodomain ℓ Y)
    (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)))
    (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧))
    (cyclicStrictBoundary ℓ Y D) source target) ∧
  R.map δ ≫ target = source ≫ L.R.map (cyclicStrictBoundary ℓ Y D)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
