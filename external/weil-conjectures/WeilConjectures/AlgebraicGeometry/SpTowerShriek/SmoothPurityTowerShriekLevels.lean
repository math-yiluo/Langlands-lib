/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityStrictCompactificationComparisonRealization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityFiniteLevelProjectionCriterion
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerLocalization
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerExchange

/-! # Compact-support laws on varying-coefficient towers

Source: blueprint operations proof (1)--(3)
(blueprint: prose-09-23).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard
  Padic Padic.coefficientExtensionIntegers
  SheafOfModules.OpenTensorNormalization.finiteTensor

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerShriek

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
