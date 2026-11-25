/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Adjoints of pairings along a lax monoidal functor

Let `G : C ⥤ D` be a lax monoidal functor between monoidal closed categories (for instance a
change of coefficients `- ⊗ᴸ_{A_n} A_m`), and let `b : X ⊗ Y ⟶ 𝟙_ C` and `b' : X' ⊗ Y' ⟶ 𝟙_ D`
be pairings related by comparison maps `c_X : X' ⟶ G X`, `c_Y : G Y ⟶ Y'` and `e : G 𝟙_ C ⟶ 𝟙_ D`:
```
X' ⊗ G Y ──X' ◁ c_Y──▶ X' ⊗ Y' ──b'──▶ 𝟙_ D
    │                                   ▲
c_X ▷ G Y                               │ e
    ▼                                   │
G X ⊗ G Y ──μ──▶ G (X ⊗ Y) ──G b──▶ G 𝟙_ C
```
Taking tensor–internal-hom adjoints, the square of adjoints
```
     G Y ──────G (curry b)──────▶ G [X, 𝟙_ C]
      │                               │ comparison
  c_Y │                               ▼
      ▼                          [X', 𝟙_ D]
      Y' ──────curry b'───────────▲
```
commutes (`CategoryTheory.MonoidalClosed.map_curry_comp_unitDualComparison`), where the comparison
`G [X, 𝟙_ C] ⟶ [G X, G 𝟙_ C] ⟶ [G X, 𝟙_ D] ⟶ [X', 𝟙_ D]` is built from
`CategoryTheory.Functor.LaxMonoidal.ihomComparison`, `e` and `c_X`. For perfect pairings this is
the square of the inverses of the adjoints (`CategoryTheory.MonoidalClosed.map_inv_curry_comp`).
This is the formal step of blueprint `theorem-poincare-duality--9`: the reduction of the adjoint of
the derived Poincaré pairing at level `n` is the adjoint at level `m`.
-/

@[expose] public section

namespace CategoryTheory.MonoidalClosed

open MonoidalCategory Functor.LaxMonoidal

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (G : C ⥤ D) [G.LaxMonoidal]

/-- The comparison `G [X, 𝟙_ C] ⟶ [X', 𝟙_ D]` of duals along a lax monoidal functor `G`, given
maps `c_X : X' ⟶ G X` and `e : G 𝟙_ C ⟶ 𝟙_ D`: the composite
```
G [X, 𝟙_ C] ──ihomComparison──▶ [G X, G 𝟙_ C] ──[G X, e]──▶ [G X, 𝟙_ D] ──pre c_X──▶ [X', 𝟙_ D]
```
-/
noncomputable def unitDualComparison {X : C} {X' : D} (cX : X' ⟶ G.obj X)
    (e : G.obj (𝟙_ C) ⟶ 𝟙_ D) :
    G.obj ((ihom X).obj (𝟙_ C)) ⟶ (ihom X').obj (𝟙_ D) :=
  (ihomComparison G X).app (𝟙_ C) ≫ (ihom (G.obj X)).map e ≫ (pre cX).app (𝟙_ D)

lemma uncurry_unitDualComparison {X : C} {X' : D} (cX : X' ⟶ G.obj X) (e : G.obj (𝟙_ C) ⟶ 𝟙_ D) :
    uncurry (unitDualComparison G cX e) =
      cX ▷ _ ≫ μ G X _ ≫ G.map ((ihom.ev X).app (𝟙_ C)) ≫ e := by
  rw [unitDualComparison, ← Category.assoc, uncurry_pre_app, uncurry_natural_right, uncurry_eq,
    ihomComparison_ev, Category.assoc]

/-- Blueprint `theorem-poincare-duality--9` (formal step): **the adjoints of compatible pairings
form a commuting square.** If the pairings `b : X ⊗ Y ⟶ 𝟙_ C` and `b' : X' ⊗ Y' ⟶ 𝟙_ D` are
compatible along the lax monoidal functor `G` through `c_X : X' ⟶ G X`, `c_Y : G Y ⟶ Y'` and
`e : G 𝟙_ C ⟶ 𝟙_ D`, then `G (curry b)` followed by the dual comparison is `c_Y ≫ curry b'`. -/
theorem map_curry_comp_unitDualComparison {X Y : C} {X' Y' : D} (b : X ⊗ Y ⟶ 𝟙_ C)
    (b' : X' ⊗ Y' ⟶ 𝟙_ D) (cX : X' ⟶ G.obj X) (cY : G.obj Y ⟶ Y') (e : G.obj (𝟙_ C) ⟶ 𝟙_ D)
    (h : X' ◁ cY ≫ b' = cX ▷ G.obj Y ≫ μ G X Y ≫ G.map b ≫ e) :
    G.map (curry b) ≫ unitDualComparison G cX e = cY ≫ curry b' := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry, h, uncurry_unitDualComparison,
    whisker_exchange_assoc, μ_natural_right_assoc, ← G.map_comp_assoc, ← uncurry_eq,
    uncurry_curry]

/-- Blueprint `theorem-poincare-duality--9`: Finite reduction of the Poincaré pairing, formal form.

In the situation of `CategoryTheory.MonoidalClosed.map_curry_comp_unitDualComparison`, if both
pairings are perfect, the square of the inverses of their adjoints commutes:
```
G [X, 𝟙_ C] ──G (curry b)⁻¹──▶ G Y
     │                           │
     │ dual comparison           │ c_Y
     ▼                           ▼
 [X', 𝟙_ D] ───(curry b')⁻¹───▶ Y'
```
-/
theorem map_inv_curry_comp {X Y : C} {X' Y' : D} {b : X ⊗ Y ⟶ 𝟙_ C} {b' : X' ⊗ Y' ⟶ 𝟙_ D}
    (hb : IsPerfectPairing b) (hb' : IsPerfectPairing b') (cX : X' ⟶ G.obj X)
    (cY : G.obj Y ⟶ Y') (e : G.obj (𝟙_ C) ⟶ 𝟙_ D)
    (h : X' ◁ cY ≫ b' = cX ▷ G.obj Y ≫ μ G X Y ≫ G.map b ≫ e) :
    G.map (hb.iso.inv) ≫ cY = unitDualComparison G cX e ≫ hb'.iso.inv := by
  have := map_curry_comp_unitDualComparison G b b' cX cY e h
  have h₁ : G.map hb.iso.hom = G.map (curry b) := rfl
  have h₂ : hb'.iso.hom = curry b' := rfl
  rw [← h₁, ← h₂] at this
  rw [Iso.eq_comp_inv, Category.assoc, ← this, ← G.map_comp_assoc, Iso.inv_hom_id, G.map_id,
    Category.id_comp]

/-- In the situation of `CategoryTheory.MonoidalClosed.map_curry_comp_unitDualComparison`, if both
pairings are perfect and the dual comparison is an isomorphism, then so is `c_Y`. In blueprint
`theorem-poincare-duality--9` this shows that the comparison map on ordinary global sections is an
isomorphism. -/
theorem isIso_of_map_curry_comp_unitDualComparison {X Y : C} {X' Y' : D} {b : X ⊗ Y ⟶ 𝟙_ C}
    {b' : X' ⊗ Y' ⟶ 𝟙_ D} (hb : IsPerfectPairing b) (hb' : IsPerfectPairing b')
    (cX : X' ⟶ G.obj X) (cY : G.obj Y ⟶ Y') (e : G.obj (𝟙_ C) ⟶ 𝟙_ D)
    [IsIso (unitDualComparison G cX e)]
    (h : X' ◁ cY ≫ b' = cX ▷ G.obj Y ≫ μ G X Y ≫ G.map b ≫ e) : IsIso cY := by
  have := map_inv_curry_comp G hb hb' cX cY e h
  have e' : cY = G.map hb.iso.hom ≫ unitDualComparison G cX e ≫ hb'.iso.inv := by
    rw [← this, ← G.map_comp_assoc, Iso.hom_inv_id, G.map_id, Category.id_comp]
  rw [e']
  infer_instance

end CategoryTheory.MonoidalClosed
