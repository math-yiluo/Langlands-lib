/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralCategoryWitnesses

/-! # The actual evaluated integral line class

Source: diagonal-tower trace (1), exact evaluation of the constant line class.
(blueprint: def-sfb-finite-evaluated-integral-line-class).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local instance 100001] finiteIntegralTowerDerived finiteIntegralTowerExt
  finiteIntegralAbDerived finiteIntegralAbExt

/-- Exact evaluation of the explicitly constructed integral line class.
Source: the constant-system construction of lineBundleClass
(blueprint: def-sfb-finite-evaluated-integral-line-class). -/
def finiteEvaluatedIntegralLineClass (T : Scheme.{u}) (n : ℕ) (L : T.Pic) :
    FiniteIntegralEvaluatedLineArrow T n :=
  mapSingleArrow (abEvaluation T n) (1 : ℤ) (lineBundleClass T L)

end AlgebraicGeometry.ProEtale.SpTowerClasses
