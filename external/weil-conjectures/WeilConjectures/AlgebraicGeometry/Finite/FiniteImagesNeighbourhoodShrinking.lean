/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Simultaneous shrinking below finitely many finite morphisms

Source: Stacks Project, Tag 0GK7, the final shrinking paragraphs.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- If open sets in finitely many finite covers contain every point above a given point,
an affine neighbourhood of that point has inverse images contained in all those opens.

Source: Stacks Project, Tag 0GK7, final shrinking paragraphs.
(blueprint: lem-weil-pbc-finite-images-neighbourhood-shrinking)

Proof: For each finite map, the image of the closed complement is closed and avoids η.
The union of these finitely many images is closed and avoids η. Choose an affine
neighbourhood inside its open complement. Membership in an inverse image outside a
prescribed open would put its image in that closed union, a contradiction. For n=0
the union is empty, so any affine neighbourhood works. No Noetherian assumption is used.
-/
theorem exists_affine_neighbourhood_below_finite_maps
    (V : Scheme.{u}) (η : V) (n : ℕ) (T : Fin n → Scheme.{u})
    (t : ∀ i, T i ⟶ V) [∀ i, IsFinite (t i)] (O : ∀ i, (T i).Opens)
    (hO : ∀ i (x : T i), t i x = η → x ∈ O i) :
    ∃ (U : V.Opens), η ∈ U ∧ IsAffineOpen U ∧ ∀ i, (t i) ⁻¹ᵁ U ≤ O i := by
  classical
  let bad (i : Fin n) := t i '' (O i : Set (T i))ᶜ
  have hbad (i : Fin n) : IsClosed (bad i) :=
    (t i).isClosedMap _ (O i).isOpen.isClosed_compl
  let W : V.Opens := ⟨(⋃ i, bad i)ᶜ, (isClosed_iUnion_of_finite hbad).isOpen_compl⟩
  have hηW : η ∈ W := by
    intro h
    obtain ⟨i, x, hx, htx⟩ := Set.mem_iUnion.mp h
    exact hx (hO i x htx)
  obtain ⟨U, hU, hηU, hUW⟩ := exists_isAffineOpen_mem_and_subset (x := η) (U := W) hηW
  refine ⟨U, hηU, hU, ?_⟩
  intro i x hx
  by_contra hxo
  exact hUW hx (Set.mem_iUnion.mpr ⟨i, x, hxo, rfl⟩)

end AlgebraicGeometry
