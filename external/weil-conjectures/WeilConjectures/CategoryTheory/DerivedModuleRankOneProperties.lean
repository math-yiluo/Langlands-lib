/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
import WeilConjectures.CategoryTheory.DerivedModuleRankOneGenerator

@[expose] public section

universe w vH

namespace CategoryTheory

open Limits

/-- The degree-zero complex on the explicit free rank-one left module is a compact
weak generator. Source: Stacks Project, Tag 0F5X, first paragraph, and Tag 07D9,
clauses (1)-(2).
(auxiliary; not a blueprint node)

Proof in words: put the left module `ULift S` in degree zero using `singleFunctor`.
Evaluation at the lifted unit identifies module maps out of `ULift S` with elements
of their target; the inverse sends x to the map s ↦ s • x. Thus this module is free
of rank one and projective. Its degree-zero complex is K-projective, so localization
computes maps from it by chain maps modulo homotopy. A chain map to K is a cycle
in K⁰, and a homotopy changes that cycle by a boundary. Consequently the additive,
natural group of maps to K[n] identifies with the additive group of Hⁿ(K).
For a family of derived objects, choose representative complexes. By
`derivedModuleDirectSums` their termwise sum represents the derived coproduct.
Direct sums of modules are exact: cycles and boundaries in a sum have finite
support, so their quotient is the sum of the cohomology modules. Under the natural
Hom/cohomology identification, the canonical map used in `IsCompactObject` is
therefore this isomorphism, proving its bijectivity. If a derived object is not
zero, some cohomology module is nonzero, since an acyclic representative is
quasi-isomorphic to zero. A nonzero element in that module gives a nonzero map
from the rank-one object into the corresponding shift, proving weak generation.
This argument works for noncommutative rings using left multiplication and for
the zero ring (where all objects are zero). The empty coproduct also gives the
zero group on both sides of the compactness comparison. -/
theorem derivedModule_rankOne_properties
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))] :
    let P := (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
      (ModuleCat.of S (ULift.{vH} S))
    IsCompactObject P ∧ IsWeakTriangulatedGenerator P := by
  dsimp
  exact ⟨derivedModule_rankOne_compact (S := S),
    derivedModule_rankOne_generator (S := S)⟩

end CategoryTheory
