/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective

@[expose] public section

universe w vH

namespace CategoryTheory

open Limits

/-- The degree-zero explicit free rank-one module is compact in the derived module
category. Source: Stacks Project, Tag 0F5X, first paragraph.
(auxiliary; not a blueprint node)

Proof in words: evaluation at the lifted unit identifies linear maps from
`ULift S` with elements of the target, with inverse x ↦ (s ↦ s • x). Thus this
module is free of rank one and projective. A chain map from its single complex
to K is a cycle in degree zero; two such maps are homotopic exactly when their
cycles differ by a boundary. Its single complex is K-projective: for an acyclic
target every cycle is a boundary, which provides such a null homotopy.
Localization is fully faithful on maps out of K-projective complexes, so the
additive group of derived maps from this object to K is naturally H⁰(K).
Represent a family of derived objects by complexes. By `derivedModuleDirectSums`,
the image of their termwise sum, with its canonical inclusions, is their derived
coproduct. In a termwise sum, cycles are finite-support families of cycles, and
boundaries are finite-support families of boundaries: choose a preimage in each
of the finitely many nonzero coordinates. Taking the quotient therefore gives
H⁰(⨁ Kᵢ) ≅ ⨁ H⁰(Kᵢ), compatibly with inclusions. Naturality of the preceding
Hom identification identifies the canonical map defining `IsCompactObject`
with this additive isomorphism, so it is bijective. For the empty family both
groups are zero. The argument uses only left modules, so needs no commutativity;
for the zero ring all modules and both comparison groups are zero.
-/
theorem derivedModule_rankOne_compact
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))] :
    IsCompactObject
      ((DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
        (ModuleCat.of S (ULift.{vH} S))) := by
  intro I E
  exact ⟨derivedModule_rankOne_comparison_injective (S := S) I E,
    derivedModule_rankOne_comparison_surjective (S := S) I E⟩

end CategoryTheory
