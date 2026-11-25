/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedProperScalarNormalization
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedOpenScalarNormalization

/-! # Fixed-module normalization of the recorded intrinsic coefficient arrow

Source: Stacks Project, Tags 00YV, 03D3 and 0GL6, and Step 3 of
lem-sp-transported-compact-scalar-site-square. This is a comparison of the two
pro-etale presentations only; no etale input or boundedness is involved.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local irreducible]
  Functor.mapDerivedCategory Functor.rightDerivedFunctor Functor.leftDerivedFunctor
  sfIntrinsicModuleEquivalence scalarPresentation directImagePresentation
  Functor.mapDerivedCategoryNatIso
  directImageScalarComparison reductionOpenScalarIso OpenScalarSite.scalarOpen
  supportPresentation FiniteCompactScalar.openRealizationIso
attribute [local implicit_reducible] sfIntrinsicDerivedEquivalence
  Equivalence.mapDerivedCategory sfIntrinsicExtensionByZero
  proEtaleConstantRingMap scalarExtensionFunctor

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
