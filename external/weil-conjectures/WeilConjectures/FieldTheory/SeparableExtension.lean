/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.TranscendentalSeparable

/-!
# Separably generated and separable field extensions

Source: Stacks Project, Algebra, Definition 10.42.1 (Tag 030O)
(blueprint: def-weil-pbc-separable-field-extension).

## Main definitions

* `Algebra.IsSeparablyGenerated`: a transcendence basis with separable algebraic extension.
* `Algebra.IsSeparableExtension`: every finitely generated subextension is separably generated.
-/

@[expose] public section

universe u v

namespace Algebra

/-- A field extension `K/k` is separable if every intermediate field finitely generated as a
field over `k` is separably generated over `k`.
Source: Stacks Project, Algebra, Definition 10.42.1 (2), Tag 030O
(blueprint: def-weil-pbc-separable-field-extension). -/
def IsSeparableExtension (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K] :
    Prop :=
  ∀ F : IntermediateField k K, F.FG → IsSeparablyGenerated k F

end Algebra
