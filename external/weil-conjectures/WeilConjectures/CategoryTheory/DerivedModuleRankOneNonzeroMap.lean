/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedModuleNonzeroClassMap
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

@[expose] public section

universe w vH

namespace CategoryTheory

open Limits

/-- Every nonzero derived module object receives a nonzero map from the rank-one
single complex into an integer shift. Source: Stacks Project, Tag 0F5X, first paragraph.
(auxiliary; not a blueprint node)

Proof in words: represent the object by a complex. Nonvanishing of the object implies
nonvanishing of some cohomology module, since an acyclic representative is zero in the
derived category. A nonzero cohomology class is represented by a cycle. Evaluation at
the lifted unit turns that cycle into a chain map from the free rank-one single complex
to the corresponding shift. The map is nonzero because its cohomology class is nonzero;
the K-projective localization calculation identifies this chain map with a derived map.
-/
theorem derivedModule_rankOne_nonzero_map
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))]
    (K : DerivedCategory (ModuleCat.{max w vH} S)) (hK : ¬ IsZero K) :
    ∃ n : ℤ, ∃ f :
      (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
        (ModuleCat.of S (ULift.{vH} S)) ⟶ K⟦n⟧, f ≠ 0 := by
  have hclass : ∃ n : ℤ, ∃ x : ((DerivedCategory.homologyFunctor
      (ModuleCat.{max w vH} S) n).obj K), x ≠ 0 := by
    by_contra h
    push Not at h
    apply hK
    apply DerivedCategory.isZero_of_forall_isZero_homology K
    intro n
    have : Subsingleton ((DerivedCategory.homologyFunctor
        (ModuleCat.{max w vH} S) n).obj K) :=
      ⟨fun a b ↦ by rw [h n a, h n b]⟩
    exact ModuleCat.isZero_of_subsingleton _
  obtain ⟨n, x, hx⟩ := hclass
  obtain ⟨f, hf⟩ := derivedModule_nonzero_class_map K n x hx
  exact ⟨n, f, hf⟩

end CategoryTheory
