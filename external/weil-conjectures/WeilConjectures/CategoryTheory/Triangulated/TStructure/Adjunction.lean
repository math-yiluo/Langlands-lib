/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Right adjoints of functors of bounded amplitude

Let `F ⊣ G` be an adjunction between pretriangulated categories equipped with t-structures
`t₁` and `t₂`. If `F` raises the upper bound by at most `N` (it sends `t₁.IsLE X n` to
`t₂.IsLE (F X) (n + N)`), then `G` lowers the lower bound by at most `N`: it sends
`t₂.IsGE Y m` to `t₁.IsGE (G Y) (m - N)`. In particular `G` preserves bounded below objects.

## Main statements

- `CategoryTheory.Triangulated.TStructure.isGE_rightAdjoint_obj`
- `CategoryTheory.Triangulated.TStructure.plus_rightAdjoint_obj`
-/

@[expose] public section

namespace CategoryTheory.Triangulated.TStructure

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] (t₁ : TStructure C) (t₂ : TStructure D)
  {F : C ⥤ D} {G : D ⥤ C}

/-- If `F` sends `t₁.IsLE X n` to `t₂.IsLE (F X) (n + N)`, then its right adjoint `G` sends
`t₂.IsGE Y m` to `t₁.IsGE (G Y) (m - N)`: a morphism `X ⟶ G Y` with `X ≤ m - N - 1` is adjoint to
a morphism `F X ⟶ Y` with `F X ≤ m - 1`, which vanishes. -/
lemma isGE_rightAdjoint_obj [F.Additive] (adj : F ⊣ G) (N : ℤ)
    (hF : ∀ (X : C) (n : ℤ), t₁.IsLE X n → t₂.IsLE (F.obj X) (n + N)) (Y : D) (m : ℤ)
    [t₂.IsGE Y m] : t₁.IsGE (G.obj Y) (m - N) := by
  have := adj.right_adjoint_additive
  rw [t₁.isGE_iff_orthogonal (m - N - 1) (m - N) (by lia)]
  intro X f hX
  have := hF X _ hX
  have h0 : (adj.homEquiv _ _).symm f = 0 := t₂.zero _ (m - N - 1 + N) m (by lia)
  rw [← (adj.homEquiv _ _).apply_symm_apply f, h0, adj.homEquiv_unit, G.map_zero, comp_zero]

/-- If `F` raises the upper bound by a constant, its right adjoint preserves bounded below
objects. -/
lemma plus_rightAdjoint_obj [F.Additive] (adj : F ⊣ G) (N : ℤ)
    (hF : ∀ (X : C) (n : ℤ), t₁.IsLE X n → t₂.IsLE (F.obj X) (n + N)) (Y : D)
    (hY : t₂.plus Y) : t₁.plus (G.obj Y) := by
  obtain ⟨m, hm⟩ := hY
  exact ⟨m - N, t₁.isGE_rightAdjoint_obj t₂ adj N hF Y m⟩

end CategoryTheory.Triangulated.TStructure
