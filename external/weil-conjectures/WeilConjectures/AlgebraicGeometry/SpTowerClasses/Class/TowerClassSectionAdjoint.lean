/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback

/-! # Explicit section carriers for tower adjunction

Source: the ordinary evaluation comparison for strict coefficient systems.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] lineModule
  Scheme.proEtaleConstantRingComparison Scheme.proEtaleRingDirectImageMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- Comparing the two section carriers traverses the fixed direct-image construction.
/-- Sectionwise ordinary adjunction with its explicit target carrier.

Source: the ordinary evaluation comparison in `def-sp-tower-shriek-data`.
This is the recorded adjoint followed by that comparison, evaluated on a chart.
(blueprint: def-sfb-tower-class-section-adjoint). -/
def sectionAdjoint
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {M : Systems Y (Arings l E Y)} {N : Systems X (Arings l E X)}
    (h : g.pull.obj M ⟶ N) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    N.val.obj (op (n, (chart f U).unop)) :=
  adjointSection l E g h n U x

/-- The explicit-carrier adjoint is the original evaluated ordinary adjoint.
Source: the definition of sectionwise evaluation.
(blueprint: def-sfb-tower-class-section-adjoint). -/
theorem sectionAdjoint_heq
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {M : Systems Y (Arings l E Y)} {N : Systems X (Arings l E X)}
    (h : g.pull.obj M ⟶ N) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    HEq (sectionAdjoint l E g h n U x) (adjointSection l E g h n U x) := HEq.rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses
