/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FinitePullbackStrictTowerData.FinitePullbackStrictTowerData

/-! # Balanced comparison of completed and finite scalar extension

Source: Stacks Project, Tags 03EK, 03EL and 07A4.
(blueprint: lem-a1-balanced-finite-tower-scalar-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.CompletedTowerIndependent.pull
open WeilConjectures.CompletedTowerIndependent
open WeilConjectures.FinitePullbackStrictTowerData
open WeilConjectures.CompletedPullbackUniverseTransportData

namespace WeilConjectures.BalancedFiniteTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

end WeilConjectures.BalancedFiniteTower
