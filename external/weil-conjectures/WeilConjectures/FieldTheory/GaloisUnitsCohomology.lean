/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Continuous Galois cohomology of separable-closure units

The coefficient group is discrete, and the Galois group has its Krull topology.
Source: Stacks Project, Tags 04JP, 04JR, 0DVG and 03QQ.
(blueprint: def-sc-galois-units-cohomology).
-/

@[expose] public section

universe u

namespace Field

variable (K : Type u) [Field K]

local instance : TopologicalSpace ((Rep.ofAlgebraAutOnUnits K (SeparableClosure K))) := ⊥
local instance : DiscreteTopology ((Rep.ofAlgebraAutOnUnits K (SeparableClosure K))) := ⟨rfl⟩

/-- The natural action of the Galois group on the discrete units of a separable closure,
written additively. Each automorphism is continuous on the discrete coefficient group.
The group itself retains the Krull topology. The action is jointly continuous because
each unit lies in a finite extension, whose fixing subgroup is open in the Krull topology.
Source: Stacks Project, Example 03QV (2).
(blueprint: def-sc-galois-units-cohomology). -/
noncomputable def galoisUnitsTopRep : TopRep ℤ (SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
  TopRep.of
    ⟨{ toFun := fun g ↦
          { toLinearMap := (Rep.ofAlgebraAutOnUnits K (SeparableClosure K)).ρ g
            cont := continuous_of_discreteTopology }
       map_one' := by
         ext x
         exact congrArg (fun f ↦ f x)
           (Rep.ofAlgebraAutOnUnits K (SeparableClosure K)).ρ.map_one
       map_mul' := by
         intro g h
         ext x
         exact congrArg (fun f ↦ f x)
           ((Rep.ofAlgebraAutOnUnits K (SeparableClosure K)).ρ.map_mul g h) }⟩

/-- The second continuous Galois cohomology of the discrete units of a separable closure.
Mathlib's homogeneous continuous cochains are used, with the Krull topology on the group
and the discrete topology on the coefficients. This is not abstract group cohomology of
the underlying group. Source: Stacks Project, Tags 04JR, 0DVG, and 03QQ.
(blueprint: def-sc-galois-units-cohomology). -/
noncomputable abbrev GaloisUnitsH2 : Type u := continuousCohomology 2 (galoisUnitsTopRep K)

end Field
