/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Pro-zero middle terms in a tower of distinguished triangles

Source: Stacks Project, Derived Categories, Tag 0G3A, zero-valued specialization
(auxiliary; not a blueprint node).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Pretriangulated

/-- In an inverse system of distinguished triangles, simultaneous eventual vanishing of the
first and third transition maps implies eventual vanishing of the middle transition maps.
Index `n : ℕ` denotes level `n + 1` of the positive-integer tower.

Source: Stacks Project, Derived Categories, Tag 0G3A, zero-valued specialization
(auxiliary; not a blueprint node).

Proof (the direct zero-valued argument recorded in the node):
1. Fix a level `n`. Choose `m ≥ n` with zero first transition `a` from `m` to `n`, using
   the outer-term hypothesis. If `u` is the first triangle arrow and `b` the middle
   transition, the first triangle-morphism square gives `u_m ≫ b = a ≫ u_n = 0`.
2. Apply `lem-weil-pbc-hom-out-of-triangle-exact` (i), namely
   `Triangle.yoneda_exact₂`, to the distinguished triangle at `m` and the object `B_n`.
   Obtain `h : C_m ⟶ B_n` with `b = v_m ≫ h`.
3. Choose `k ≥ m` with zero third transition from `k` to `m`. The second
   triangle-morphism square gives `b_km ≫ v_m = v_k ≫ c_km = 0`.
   The functor composition law (def-weil-inverse-system) now gives
   `b_kn = b_km ≫ b_mn = b_km ≫ v_m ≫ h = 0`.
4. Since `n ≤ m ≤ k`, this proves the required vanishing at every level. -/
theorem proZero_middle_of_distinguished_tower
    {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ i : ℤ, (shiftFunctor D i).Additive] [Pretriangulated D] [IsTriangulated D]
    (T : ℕᵒᵖ ⥤ Triangle D)
    (hT : ∀ n : ℕ, T.obj (Opposite.op n) ∈ distTriang D)
    (hAC : ∀ n : ℕ, ∃ (k : ℕ) (hnk : n ≤ k),
      (T.map (homOfLE hnk).op).hom₁ = 0 ∧
      (T.map (homOfLE hnk).op).hom₃ = 0) :
    ∀ n : ℕ, ∃ (k : ℕ) (hnk : n ≤ k), (T.map (homOfLE hnk).op).hom₂ = 0 := by
  intro n
  obtain ⟨m, hnm, ha, _⟩ := hAC n
  obtain ⟨h, hh⟩ := Triangle.yoneda_exact₂ _ (hT m)
    (T.map (homOfLE hnm).op).hom₂ (by
      rw [(T.map (homOfLE hnm).op).comm₁, ha, zero_comp])
  obtain ⟨k, hmk, _, hc⟩ := hAC m
  refine ⟨k, hnm.trans hmk, ?_⟩
  have hcomp : (homOfLE (hnm.trans hmk)).op =
      (homOfLE hmk).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
  rw [hcomp, T.map_comp, comp_hom₂, hh, ← Category.assoc,
    ← (T.map (homOfLE hmk).op).comm₂, hc, comp_zero, zero_comp]

end CategoryTheory.Pretriangulated
