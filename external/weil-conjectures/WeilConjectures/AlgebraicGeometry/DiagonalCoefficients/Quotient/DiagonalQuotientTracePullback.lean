/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFamilyPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalPullbackSquares
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Quotient.DiagonalQuotientLinePullbackNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarUnitPullbackNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarExchangeCube
import WeilConjectures.AlgebraicGeometry.InternalPullNormalizationExistence
import all WeilConjectures.AlgebraicGeometry.InternalScalarRestrictionMateNormalization

/-! # Scalar pasting of the three trace squares

Source: diagonal tower coefficient changes, paragraph (3), scalar base change.
(blueprint: lem-diagonal-quotient-trace-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedUpper derivedLower
  derivedScalars modelExchange singlePullback PullEndpoint.shift Endpoint.shift

set_option allowUnsafeReducibility true in
attribute [local reducible] derivedLower derivedUpper derivedScalars
  QuotientChange.L QuotientChange.D
  CondensedRing.moduleObjectDerivedPullback

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
