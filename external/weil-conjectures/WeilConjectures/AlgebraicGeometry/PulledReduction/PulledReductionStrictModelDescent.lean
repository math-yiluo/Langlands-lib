/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PulledReduction.PulledReductionComparisonData

/-! # Descent of the augmented pulled reduction model

## References

* Stacks 06YY, 07A4, and 099N(5)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.PulledReduction
attribute [local instance] ordinaryReductionTarget_preservesZeroMorphisms
attribute [local instance] completedModulePullback_additive
attribute [local instance] completedTowerModulePullback_additive
attribute [local instance] completedReductionModuleTowerFunctor_additive
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X Y : Scheme.{t}} (g : X ⟶ Y)

end AlgebraicGeometry.Scheme.PulledReduction
