/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.System.SystemTensorReductionFormula
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictSystemGeometricRealization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictPlusComparisonsRealization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictPlusEvaluationRealization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictOpenWordEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictFiniteWordIdentification
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # Assembly of normalized strict compactification comparisons

Source: blueprint operations proof (2).
(blueprint: lem-sp-strict-compactification-comparison-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek
