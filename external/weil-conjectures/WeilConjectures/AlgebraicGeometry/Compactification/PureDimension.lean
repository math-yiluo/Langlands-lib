/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension

/-! # Pure dimension of a scheme

Source: Stacks Project, Topology, Definition 5.10.4, Tag 0058,
with the common dimension fixed to be `d` (blueprint: def-weil-pure-dimension).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A scheme has pure dimension `d` if every irreducible component of its underlying
space, equipped with the subspace topology, has Krull dimension `d`.
The empty scheme has pure dimension `d` for every `d`, since it has no irreducible components.
Source: Stacks Project, Topology, Definition 5.10.4, Tag 0058, fixing the common dimension.
(blueprint: def-weil-pure-dimension) -/
def Scheme.IsPureDimension (X : Scheme.{u}) (d : ℕ) : Prop :=
  ∀ Z : Set X, Z ∈ irreducibleComponents X → topologicalKrullDim Z = (d : WithBot ℕ∞)

end AlgebraicGeometry
