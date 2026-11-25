/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CompletedTowerIndependent.IntegralCompletedTowerPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ImmersionCompletedPullback.SfImmersionCompletedPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReduction

/-! # Published completed-pullback universe transport

Source: Stacks 03EK/03EL, 099N(5)
(blueprint: def-a1-completed-pullback-universe-transport-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u r s v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.unrestrictedIntegralReductionFunctor
  WeilConjectures.CompletedTowerIndependent.pull
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.CompletedPullbackUniverseTransportData

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The recorded ordinary reduction, with its specified completed scalar action.
Source: Stacks 099N(5) (blueprint: def-a1-completed-pullback-universe-transport-data). -/
def ordinaryReduction (W : Scheme.{t}) (n : ℕ) : Modules l E W ⥤ Modules l E W :=
  unrestrictedIntegralReductionFunctor l E W n ⋙
    SheafOfModules.restrictScalars
      (limit.π (integralCoefficientSheafSystem l E W) (op n))

variable {X Y : Scheme.{t}} (g : X ⟶ Y)

end WeilConjectures.CompletedPullbackUniverseTransportData
