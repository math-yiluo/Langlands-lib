/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictLocalizationMap
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Equal-degree finite trait covers and their product

Source: blueprint `lemma-tangent-cones-on-cover`, clause (ii), with the
normalization input from proof (i) (blueprint: lem-trf-finite-trait-cover-product).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace AlgebraicGeometry.FiniteTraitCoverProduct

/-- A smooth pointed curve over an algebraically closed field.
Source: blueprint `lemma-tangent-cones-on-cover`, clause (ii)
(blueprint: lem-trf-finite-trait-cover-product). -/
structure CurvePoint (k : Type u) [Field k] [IsAlgClosed k] where
  C : Scheme.{u}
  f : C ⟶ Spec (.of k)
  curve : IsCurve f
  smooth : Smooth f
  relativeDimension : SmoothOfRelativeDimension 1 f
  x : Spec (.of k) ⟶ C
  x_f : x ≫ f = 𝟙 _

attribute [instance] CurvePoint.curve CurvePoint.smooth CurvePoint.relativeDimension

end AlgebraicGeometry.FiniteTraitCoverProduct
