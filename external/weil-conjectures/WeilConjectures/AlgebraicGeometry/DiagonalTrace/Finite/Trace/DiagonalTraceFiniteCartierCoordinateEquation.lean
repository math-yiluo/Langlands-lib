/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteBoundarySourceAlgebra
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteCartierArrow

/-! # Coordinates for the finite supported boundary equation -/

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
  diagonalScalarExtension
  diagonalScalarAdjunction diagonalIntegralBoundary
  diagonalSingleLimitComparison diagonalExactFunctorExtImage
  diagonalShiftedSingleLimitComparison diagonalCompletedGenerator
  SpTowerClasses.lineModule Coefficients.unitMap
  completedSupportedUnit

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The published finite Cartier map equals the generic finite coordinate composite.
This definition names the explicit equation and asserts no property.
Source: diagonal trace proof (2), finite Cartier endpoint.
(blueprint: def-sfb-diagonal-trace-finite-cartier-coordinate-map-equation). -/
@[irreducible] def finiteCartierCoordinateMapEquation
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y))) : Prop :=
    a.cartierMap l Y hY c r k n L
        (cartierResidueReducedPro l (Fact.out : l.Prime) (n + 1)
          (diagonalImmersion Y) (diagonalImmersion_cartier Y)
          (diagonalSurface_power_unit l Y hY n)) =
      finiteBoundaryCoordinateMap (diagonalCompletedRestriction l (diagonalSurface Y))
        r.F L _
        (SpTowerClasses.coefficient (diagonalSurface Y)
          (SpTowerClasses.Arings l (ULift.{u} (Padic l)) (diagonalSurface Y)))
        (SpTowerClasses.lineModule l (ULift.{u} (Padic l)) c) n a.coefficient
        k.coefficientProjection
        ((diagonalFiniteToPadic l n (diagonalSurface Y)).map
          (Scheme.proEtaleConstantDirectImageMap (diagonalImmersion Y)
            (ModuleCat.{u + 1} (diagonalResidue.{u} l n))
            (ModuleCat.of (diagonalResidue.{u} l n) (diagonalResidue.{u} l n))))
        (finiteCartierArrow l Y hY n) a.line

end AlgebraicGeometry.ProEtale.DiagonalTrace
