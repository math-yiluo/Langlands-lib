/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator

/-!
# Compactly generated triangulated categories

Source: Stacks Project, Derived Categories, Definition 13.37.5 (Tag 09SQ)
(blueprint: def-pc-compactly-generated).
-/

@[expose] public section

universe w v u

open CategoryTheory.Limits

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] [HasCoproducts.{w} C]

/-- A triangulated category with arbitrary coproducts is compactly generated when some
set-indexed family consists of compact objects and its coproduct generates the category
(Stacks, Tag 09SQ) (blueprint: def-pc-compactly-generated). -/
def IsCompactlyGeneratedTriangulated : Prop :=
  ∃ (I : Type w) (E : I → C),
    (∀ i : I, IsCompactObject (E i)) ∧ IsTriangulatedGeneratingFamily E

end CategoryTheory
