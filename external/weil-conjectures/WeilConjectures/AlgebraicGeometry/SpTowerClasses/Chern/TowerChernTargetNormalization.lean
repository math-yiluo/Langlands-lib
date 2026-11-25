/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.ChernData.TowerChernTargetNormalizationData

/-! # The concrete integral target normalization

Source: classes (2) (blueprint: lem-sp-tower-chern-target-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.singleFunctors
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Extract the positive Kummer-boundary normalization at the actual coefficient towers.

Source: classes (2), normalization of integral reduction
(blueprint: lem-sp-tower-chern-target-normalization).

Proof: apply the proved target-normalization projection to the actual R and A
coefficient diagrams and their scalar generator. -/
theorem chern_target_normalization {T : Scheme.{u}} (c : Chern l E T)
    (n : c.Normalized l E) :
    c.rootNormalized l T (Rrings l T) (Arings l E T)
      (coefficientSystemMap l E T) := by
  exact chern_integral_target_normalization l T (Rrings l T) (Arings l E T)
    (coefficientSystemMap l E T) c (scalarGenerator l E T) n

end AlgebraicGeometry.ProEtale.SpTowerClasses
