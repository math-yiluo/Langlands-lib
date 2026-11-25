/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.CompactlyGenerated
import WeilConjectures.CategoryTheory.DerivedModuleRankOneProperties

/-! # Compact generation of the derived category of modules

Source: Stacks Project, Tags 0F5X and 07D9.
-/

@[expose] public section

universe w vH

namespace CategoryTheory

open Limits

/-- The derived module category is compactly generated in the modules' universe.
Source: Stacks Project, Tag 0F5X, first paragraph, and Tag 07D9.
(auxiliary; not a blueprint node)

Proof in words: let P be the single complex in degree zero on the free left S-module
of rank one, represented at the modules' universe by ULift S. It is K-projective.
Maps from P into an arbitrary derived object compute its degree-zero cohomology;
more generally, maps from P into the n-th shift compute degree-n cohomology.
This identification is additive and natural in the derived object. The universal
property of module direct sums and the fact that cohomology commutes with exact
termwise sums identify the canonical direct sum of Hom groups out of P with the
Hom group into the derived coproduct. Thus P is compact. If all maps from P into
all shifts of K vanish, every cohomology module of K vanishes, so its representative
is acyclic and K is zero. Hence P is a weak generator. Take the singleton family
with value P; its coproduct is canonically isomorphic to P, so it is a compact
triangulated generating family. For the zero ring the category is zero and the
same argument is valid; no nonzero-ring hypothesis is needed. The argument uses
only left-module structures and does not require commutativity of S. -/
theorem derivedModuleCompactGeneration
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))] :
    IsCompactlyGeneratedTriangulated.{max w vH}
      (DerivedCategory (ModuleCat.{max w vH} S)) := by
  classical
  let P := (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
    (ModuleCat.of S (ULift.{vH} S))
  obtain ⟨hPcompact, hPgen⟩ := derivedModule_rankOne_properties (S := S)
  let I : Type (max w vH) := ULift.{max w vH} PUnit
  let E : I → DerivedCategory (ModuleCat.{max w vH} S) := fun _ => P
  let e : (∐ E) ≅ P := coproductUniqueIso E
  have hgenE : IsWeakTriangulatedGenerator (∐ E) := by
    intro K hK
    obtain ⟨n, f, hf⟩ := hPgen K hK
    refine ⟨n, e.hom ≫ f, ?_⟩
    intro hz
    apply hf
    have hh : e.hom ≫ f = e.hom ≫ (0 : P ⟶ K⟦n⟧) := by
      simpa only [comp_zero] using hz
    exact (cancel_epi e.hom).1 hh
  refine ⟨I, E, ?_, hgenE⟩
  intro i
  exact hPcompact

end CategoryTheory
