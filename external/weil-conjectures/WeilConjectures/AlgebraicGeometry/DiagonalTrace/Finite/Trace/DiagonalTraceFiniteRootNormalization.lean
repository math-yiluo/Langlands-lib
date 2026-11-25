/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit

/-! # The normalized finite root identification of the supported Cartier class -/

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

/-- Normalize the finite root endpoint on its actual underlying root sheaf.
Source: diagonal-limit clause (3), root normalization of the positive Cartier class.
(blueprint: def-sfb-diagonal-trace-finite-root-normalization). -/
@[irreducible]
def FiniteRootNormalization
    (l : ℕ) [Fact l.Prime]
    (Y : Scheme.{u}) (hY : IsUnit (l : Γ(Y, ⊤)))
    (H : DiagonalSystems l (diagonalSurface Y))
    (roots : H ⋙ diagonalForget l (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) l (Fact.out : l.Prime))
    (n : ℕ) (t : H.obj (op n) ≅
      (diagonalFiniteToPadic l n (diagonalSurface Y)).obj
        (geoCartierLine (diagonalResidue.{u} l n) (l ^ (n + 1))
          (cartierResidue_cast l (n + 1)) (diagonalSurface Y))) : Prop :=
  HEq ((diagonalForget l (diagonalSurface Y)).map t.hom)
        (roots.hom.app (op n) ≫
          cartierProRootMap (diagonalResidue.{u} l n) (l ^ (n + 1))
            (cartierResidue_cast l (n + 1)) (diagonalSurface Y)
            (pow_pos (Fact.out : l.Prime).pos _) (diagonalSurface_power_unit l Y hY n))

end AlgebraicGeometry.ProEtale.DiagonalTrace
