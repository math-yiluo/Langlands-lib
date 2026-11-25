/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFamilyPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalPullbackSquares
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Quotient.DiagonalQuotientLinePullbackNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Supported.DiagonalSupportedPullbackScalarNormalization

/-! # Scalar transport of the diagonal class square

Source: diagonal tower coefficient changes, paragraph (3), scalar base change.
(blueprint: lem-diagonal-quotient-class-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedUpper derivedLower
  derivedScalars modelExchange singlePullback PullEndpoint.shift Endpoint.shift
  scalarPullbackComparison Functor.leftDerivedFunctor Functor.mapDerivedCategory
  spIntegralTwist spIntegralComparison

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
