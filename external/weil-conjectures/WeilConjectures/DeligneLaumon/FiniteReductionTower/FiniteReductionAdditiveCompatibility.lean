/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CompletedTowerIndependent.IntegralCompletedTowerPullbackUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! # Additive compatibility of the actual finite pullback tower

Source: Stacks, Tags 014E, 0FNH, 06XN.
(blueprint: lem-a1-finite-reduction-additive-compatibility)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
attribute [local implicit_reducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.integralCoefficientSheaf WeilConjectures.integralCoefficientSheafSystem
  CategoryTheory.sheafCompose WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.integralCoefficientCommRingSheaf SheafOfModules.restrictScalars
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.CompletedTowerIndependent
namespace WeilConjectures.FiniteReductionTower
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {X Y : Scheme.{t}} (g : X ⟶ Y)

end WeilConjectures.FiniteReductionTower
