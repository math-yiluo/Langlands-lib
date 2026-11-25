/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts

import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

set_option linter.privateModule false

/-! # Rank-zero chart coefficient normalization

Source: blueprint vector-bundle purity, paragraph 2, prescribed counit on a frame.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  vectorIntegrationChart upperStar Functor.leftDerivedFunctor
  Functor.mapDerivedCategory HasDerivedCategory.ofIsGrothendieckAbelian
  leftDerivedUpperStarComp leftDerivedUpperStarId

set_option allowUnsafeReducibility true in
attribute [local reducible] affineTraceTower affineTraceProjection affineLinearBaseCoefficient
attribute [local implicit_reducible] Scheme.Modules vectorIntegrationCoefficient
  vectorIntegrationChartCoefficient vectorIntegrationBaseCoefficientPullback
  affineLinearCoefficientDescent

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private lemma named_compositor
    (A : Type (u + 1)) [CommRing A] {X Y Z : Scheme.{u}}
    (r : X ⟶ Y) (v : Y ⟶ Z) (k : X ⟶ Z) (e : k = r ≫ v) :
    eqToIso (congrArg (ordinaryFinitePullback A) e) ≪≫
        leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v =
      leftDerivedUpperStarComp (ModuleCat.{u + 1} A) r v k e := by
  subst k
  simp only [eqToIso_refl, Iso.refl_trans]

private lemma pullback_id_eq (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :
    affineLinearPullbackId A S = leftDerivedUpperStarId (ModuleCat.{u + 1} A) S := by
  simp [affineLinearPullbackId, leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
    leftDerivedUpperStarIsoMapDerivedCategory]

end AlgebraicGeometry.Etale
