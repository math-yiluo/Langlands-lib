/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteBoundarySourceAlgebra

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

/-- The finite Cartier map expands to the generic coordinate composite for every class.
Source: diagonal trace proof (2), finite Cartier endpoint.
(blueprint: lem-sfb-diagonal-trace-finite-cartier-map-expansion).
Proof: expand the two composites and the coefficient unit map. Both use the same
coefficient projection, exact single coordinates, finite class image and shifted
line coordinates. Their equality is definitional. -/
theorem supportedFiniteCartierMap_expansion
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (c : SpTowerClasses.Chern l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (r : Restriction l (ULift.{u} (Padic l)) (diagonalSurface Y))
    (k : Coefficients l (ULift.{u} (Padic l)) (diagonalSurface Y) c r)
    (n : ℕ) (a : SupportedFiniteBoundaryFrame l Y hY c r k n)
    (L : DiagonalRlim (DiagonalMod l (diagonalSurface Y)))
    (z : GeoCartierClass (diagonalResidue.{u} l n) (l ^ (n + 1))
      (cartierResidue_cast l (n + 1)) (diagonalImmersion Y)) :
    a.cartierMap l Y hY c r k n L z =
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
        (diagonalExactFunctorExtImage (diagonalFiniteToPadic l n (diagonalSurface Y)) z).hom
        a.line := by
  with_unfolding_all rfl

end AlgebraicGeometry.ProEtale.DiagonalTrace
