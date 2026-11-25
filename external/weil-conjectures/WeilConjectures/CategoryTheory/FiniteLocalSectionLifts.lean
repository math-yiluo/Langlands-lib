/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Simultaneous local lifts of finitely many sections

Source: Stacks, Sites, Tag 00Z5, finite intersections of covering sieves, and the
local-surjectivity criterion in Mathlib/CategoryTheory/Sites/LocallySurjective.lean.
-/

@[expose] public section
set_option autoImplicit false
universe u v w z t
open CategoryTheory Opposite
namespace CategoryTheory.Presheaf

/-- Finitely many sections of a locally surjective presheaf map lift on a common cover.
In particular, finitely many entries in a sheafified constant ring are simultaneously
constant after refinement, by applying this to its sheafification unit.

Source: Stacks, Sites, Tag 00Z5; Mathlib `Presheaf.imageSieve_mem`.
(auxiliary; not a blueprint node).

Proof: each section has a covering image sieve. Intersect these sieves over the finite
index set; the empty intersection is maximal, and binary intersections preserve covering.
Every member of this common sieve admits a preimage of each section. Choose these
preimages separately, giving the asserted finite tuple. -/
theorem finite_local_section_lifts
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {D : Type w} [Category.{z} D] {FD : D → D → Type*} {CD : D → Type t}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    {F G : Cᵒᵖ ⥤ D} (q : F ⟶ G) [IsLocallySurjective J q]
    {U : C} {ι : Type*} [Finite ι] (s : ι → ToType (G.obj (op U))) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∃ a : ι → ToType (F.obj (op V)), ∀ i, q.app (op V) (a i) = G.map f.op (s i) := by
  classical
  let := Fintype.ofFinite ι
  have h (b : Finset ι) : ∃ S : Sieve U, S ∈ J U ∧
      ∀ (V : C) (f : V ⟶ U), S f →
        ∀ i ∈ b, ∃ a : ToType (F.obj (op V)), q.app (op V) a = G.map f.op (s i) := by
    induction b using Finset.induction_on with
    | empty =>
      exact ⟨⊤, J.top_mem U, fun _ _ _ i hi ↦ False.elim (Finset.notMem_empty i hi)⟩
    | @insert i b hi ih =>
      obtain ⟨S, hS, hs⟩ := ih
      refine ⟨imageSieve q (s i) ⊓ S,
        J.intersection_covering (imageSieve_mem J q (s i)) hS, ?_⟩
      intro V f hf j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hf.1
      · exact hs V f hf.2 j hj
  obtain ⟨S, hS, hs⟩ := h Finset.univ
  refine ⟨S, hS, ?_⟩
  intro V f hf
  choose a ha using fun i ↦ hs V f hf i (Finset.mem_univ i)
  exact ⟨a, ha⟩

end CategoryTheory.Presheaf
