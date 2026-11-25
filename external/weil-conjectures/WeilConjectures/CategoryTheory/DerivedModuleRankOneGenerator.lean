/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneNonzeroMap

@[expose] public section

universe w vH

namespace CategoryTheory

open Limits

/-- The degree-zero explicit free rank-one module is a weak triangulated generator
of the derived module category. Source: Stacks Project, Tag 0F5X, first paragraph.
(auxiliary; not a blueprint node)

Proof in words: choose a representative complex L of a derived object K.
If all cohomology modules of L vanish, the map from the zero complex to L is
a quasi-isomorphism, so becomes an isomorphism after localization and K is zero.
Thus a nonzero K has Hⁿ(L) ≠ 0 for some integer n. Choose a cycle z representing
a nonzero class there. Evaluation at the lifted unit identifies linear maps
from `ULift S` with elements; the map s ↦ s • z therefore defines a chain map
from its degree-zero single complex to L[n]. Such chain maps are homotopic
exactly when their cycles differ by a boundary. The single complex is
K-projective: every map from it to an acyclic complex is null homotopic, since
its degree-zero cycle is a boundary. Localization consequently identifies its
homotopy maps with its derived maps. The map represented by z is nonzero in
the derived category, since its cohomology class is nonzero. Transport along
the representative isomorphism gives the required nonzero map to K[n].
This works for every left-module ring; for the zero ring every complex is
zero and the nonzero-object premise is impossible. No coproduct fact is used.
-/
theorem derivedModule_rankOne_generator
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))] :
    IsWeakTriangulatedGenerator
      ((DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
        (ModuleCat.of S (ULift.{vH} S))) := by
  intro K hK
  exact derivedModule_rankOne_nonzero_map (S := S) K hK

end CategoryTheory
