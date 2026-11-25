/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurCompletedReindexingData

/-! # PurReindexingDerivedMates

## References

* Stacks Tags 08BJ, 0FND and 07A7
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.privateModule false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] completedAdicChangeData completedReductionCoefficient
attribute [local irreducible] proEtaleRingModulePullback
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
attribute [local instance 2000] reductionModulesHasDerivedCategory reductionTowerHasDerivedCategory
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The ordinary isomorphism-square mate localizes to the two specified derived
mates, with their K-injective representative equations. -/
theorem purReindexingDerivedMates
    {X' X Y' Y : Scheme.{t}}
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    [IsIso v] [IsIso g] (sq : ChosenCartesianSquare v p' p g)
    [IsIso (purReindexingModuleMate d sq)] :
  PurCompletedReindexingSquareDerived d sq ∧
  PurCompletedReindexingSquareDerivedTowers d sq ∧
  PurCompletedReindexingSquareDerivedUnits d sq ∧
  PurCompletedReindexingSquareDerivedTowerUnits d sq := by sorry

end AlgebraicGeometry.Scheme
