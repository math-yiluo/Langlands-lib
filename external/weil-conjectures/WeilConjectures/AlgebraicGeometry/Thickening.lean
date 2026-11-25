/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-!
# Thickenings of schemes

Source: Stacks Project, More on Morphisms, Definition 37.2.1 (Tag 04EX),
and Definition 37.11.1 (Tag 02H0) (blueprint: def-sbc-first-order-thickening).

For any of the predicates below, a thickening over `S` additionally has
`[T.Over S]`, `[T'.Over S]`, and `[i.IsOver S]`. A thickening of affine
schemes additionally has `[IsAffine T]` and `[IsAffine T']`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- (blueprint: def-sbc-first-order-thickening) A thickening is a closed immersion
surjective on underlying points (Stacks Project, Tag 04EX, item 1). -/
def IsThickening {T T' : Scheme.{u}} (i : T ⟶ T') : Prop :=
  IsClosedImmersion i ∧ Surjective i

/-- (blueprint: def-sbc-first-order-thickening) A first order thickening is a closed
immersion whose defining ideal sheaf has square zero (Stacks Project, Tag 04EX,
item 2). The ideal sheaf is `i.ker` on `T'`. -/
def IsFirstOrderThickening {T T' : Scheme.{u}} (i : T ⟶ T') : Prop :=
  IsClosedImmersion i ∧ i.ker ^ 2 = ⊥

/-- (blueprint: def-sbc-first-order-thickening) An `n`th order thickening is a
closed immersion whose defining ideal sheaf has `(n + 1)`st power zero
(Stacks Project, Tag 04EX, item 4). -/
def IsNthOrderThickening {T T' : Scheme.{u}} (n : ℕ) (i : T ⟶ T') : Prop :=
  IsClosedImmersion i ∧ i.ker ^ (n + 1) = ⊥

/-- (blueprint: def-sbc-first-order-thickening) A finite order thickening is a
closed immersion whose defining ideal sheaf is nilpotent: its `(n + 1)`st
power is zero for some `n : ℕ` (Stacks Project, Tag 04EX, item 3). -/
def IsFiniteOrderThickening {T T' : Scheme.{u}} (i : T ⟶ T') : Prop :=
  ∃ n : ℕ, IsNthOrderThickening n i

end AlgebraicGeometry
