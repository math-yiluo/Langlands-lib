/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit

/-! # The ordinary supported-source cone normalization -/

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

/-- The ordinary source cone has the canonical integral generator at every level.
This is the source-cone equation in IsDiagonalLimit, named without changing it.
Source: diagonal-limit clause (3), normalization of the supported source.
(blueprint: def-sfb-diagonal-trace-supported-source-cone-normalization). -/
@[irreducible]
def SupportedSourceConeNormalization (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (D : DiagonalReductionPresentation l (diagonalScalarExtension l (diagonalSurface Y)))
    (s : (diagonalCompletedRestriction l (diagonalSurface Y)).obj
      (diagonalCompletedSource l Y) ≅ limit (D.E.obj (diagonalIntegralSource Y))) : Prop :=
  ∀ n : ℕ,
      diagonalCompletedGenerator l Y ≫ (diagonalForget l (diagonalSurface Y)).map
          (s.hom ≫ limit.π (D.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction l (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget l (diagonalSurface Y)).map ((D.π n).app (diagonalIntegralSource Y))

end AlgebraicGeometry.ProEtale.DiagonalTrace
