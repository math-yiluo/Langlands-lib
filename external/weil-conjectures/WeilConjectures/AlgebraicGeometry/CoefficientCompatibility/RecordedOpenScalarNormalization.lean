/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactScalarCoordinates
import all WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteOpenScalarRealizationTransport
import all WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteOpenScalarSiteTransport
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarCounitSquare

/-! # Realization normalization for the open scalar factor

Source: Stacks Tags 00YV, 03DI and 07A6; the open-factor argument in
`lem-sp-recorded-compact-scalar-fixed-normalization`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local irreducible] sfIntrinsicModuleEquivalence
attribute [local implicit_reducible] proEtaleConstantRingMap scalarExtensionFunctor

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
