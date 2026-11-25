/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Weak generators of a triangulated category

Source: Stacks Project, Derived Categories, Definition 13.36.3 (Tag 09SJ), and the
set-indexed generating-family convention (blueprint: def-pc-generators).

## Main definitions

- `CategoryTheory.IsWeakTriangulatedGenerator`: a generator detected by maps into shifts.
- `CategoryTheory.IsTriangulatedGeneratingFamily`: a family whose coproduct is a generator.
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- An object `E` is a weak generator if every nonzero object `K` receives a nonzero
map from `E` into some integer shift of `K` (Stacks, Tag 09SJ, clause (3))
(blueprint: def-pc-generators). -/
def IsWeakTriangulatedGenerator (E : C) : Prop :=
  ∀ K : C, ¬ IsZero K → ∃ n : ℤ, ∃ f : E ⟶ K⟦n⟧, f ≠ 0

/-- A set-indexed family with an existing coproduct generates when its coproduct is a
weak generator (Stacks, Tag 09SJ, and the generating-family convention)
(blueprint: def-pc-generators). -/
def IsTriangulatedGeneratingFamily {I : Type w} (E : I → C) [HasCoproduct E] : Prop :=
  IsWeakTriangulatedGenerator (∐ E)

end CategoryTheory
