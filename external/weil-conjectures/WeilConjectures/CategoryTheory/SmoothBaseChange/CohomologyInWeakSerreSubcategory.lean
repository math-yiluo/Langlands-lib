/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty

/-!
# Cohomology in a weak Serre class

Source: Stacks Project, Tag 06UQ, label `lemma-cohomology-in-serre-subcategory`,
`derived.tex:5935-5960` (blueprint: lem-sbc-cohomology-in-weak-serre-subcategory).
-/

@[expose] public section

universe w v u

open CategoryTheory

namespace CategoryTheory

/-- If `P` is a weak Serre class in an abelian category, the derived objects whose
cohomology lies in `P`, together with their bounded-below and bounded intersections,
form full triangulated subcategories. (blueprint: lem-sbc-cohomology-in-weak-serre-subcategory)

Source: Stacks Project, Tag 06UQ, `lemma-cohomology-in-serre-subcategory`, with the
weak Serre hypotheses expanded by Homology, Tag 0754.
-/
lemma cohomology_in_weak_serre_subcategory
    {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
    (P : ObjectProperty A)
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels]
    [P.IsClosedUnderExtensions] :
    (DerivedCategory.homologyProperty P).IsTriangulated ∧
      ((DerivedCategory.homologyProperty P ⊓
        DerivedCategory.TStructure.t.plus).IsTriangulated) ∧
      ((DerivedCategory.homologyProperty P ⊓
        DerivedCategory.TStructure.t.bounded).IsTriangulated) := by
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end CategoryTheory
