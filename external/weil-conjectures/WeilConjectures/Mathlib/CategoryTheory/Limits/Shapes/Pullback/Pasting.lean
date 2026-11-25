/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Base change of inverse images

If `N` is the inverse image of `h : N ⟶ X` along `π : B ⟶ X` (the square `(c, 𝟙 N, π, h)` is
cartesian), then this persists after base change: for `G_B = B ×_X G_X` and morphisms
`G_N ⟶ G_B`, `G_N ⟶ G_X` over `N ⟶ B`, `N ⟶ X` along any `G_N ⟶ N`, the square
`(G_N ⟶ G_B, 𝟙 G_N, G_B ⟶ G_X, G_N ⟶ G_X)` is cartesian
(`CategoryTheory.IsPullback.of_id_of_isPullback`).

-/

@[expose] public section

namespace CategoryTheory.IsPullback

variable {C : Type*} [Category* C]

/-- Base change of an inverse image: if `N = B ×_X N` along `π : B ⟶ X` and `h : N ⟶ X`, and
`G_B = B ×_X G_X`, then for morphisms `G_N ⟶ G_B`, `G_N ⟶ G_X` lying over `N ⟶ B`, `N ⟶ X`
along `G_N ⟶ N`, also `G_N = G_B ×_{G_X} G_N`: the square on the left is cartesian if the one on
the right is, the left one maps to the right one along `jN`, `jB`, `jX`, and `(jB, πG, π, jX)` is
cartesian.
```
G_N --cG--> G_B          N --c--> B
 |           |           |        |
 𝟙          πG           𝟙        π
 v           v           v        v
G_N --hG--> G_X          N --h--> X
```
-/
lemma of_id_of_isPullback {N B X GN GB GX : C} {c : N ⟶ B} {π : B ⟶ X} {h : N ⟶ X}
    {jN : GN ⟶ N} {jB : GB ⟶ B} {jX : GX ⟶ X} {cG : GN ⟶ GB} {πG : GB ⟶ GX} {hG : GN ⟶ GX}
    (hpb : IsPullback c (𝟙 N) π h) (hR : IsPullback jB πG π jX) (hc : cG ≫ jB = jN ≫ c)
    (hh : hG ≫ jX = jN ≫ h) (hcπ : cG ≫ πG = hG) : IsPullback cG (𝟙 GN) πG hG := by
  refine IsPullback.of_right ?_ (by rw [hcπ, Category.id_comp]) hR
  rw [hc, hh]
  exact (IsPullback.id_vert jN).paste_horiz hpb

end CategoryTheory.IsPullback
