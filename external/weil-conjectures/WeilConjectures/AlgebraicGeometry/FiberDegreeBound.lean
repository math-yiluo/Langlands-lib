/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

/-!
# Bounds on the degrees of scheme-theoretic fibres

Source: Stacks Project, Morphisms, Section 29.56 and Definition Tag 03J4
(blueprint: def-weil-pbc-fibre-degree-bound).

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.BoundsFiberDegrees`: a bound for all fibre degrees.
* `AlgebraicGeometry.Scheme.Hom.HasUniversallyBoundedFibers`: existence of such a bound.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- An integer `n ≥ 0` bounds the degrees of the fibres of `f` if every fibre is finite
over its residue field and its degree is at most `n` (Stacks, Definition Tag 03J4;
blueprint: def-weil-pbc-fibre-degree-bound). 
(blueprint: def-weil-pbc-fibre-degree-bound)
-/
def BoundsFiberDegrees {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ y : Y, IsFinite (f.fiberToSpecResidueField y) ∧
    (f.fiberToSpecResidueField y).finrankΓ ≤ n

/-- The fibres of `f` are universally bounded if one nonnegative integer bounds the
degree of every fibre (Stacks, Definition Tag 03J4).
(blueprint: def-weil-pbc-fibre-degree-bound) -/
def HasUniversallyBoundedFibers {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∃ n : ℕ, BoundsFiberDegrees f n

end AlgebraicGeometry.Scheme.Hom
