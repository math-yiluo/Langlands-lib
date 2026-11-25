/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.Basic
public import Mathlib.Order.SuccPred.Basic

/-!
# Colimits of interleaved diagrams

If two diagrams `F₁ F₂ : ι ⥤ A` over a partial order with a successor function are interleaved
by a natural transformation `F₁ ⟶ F₂` and maps `F₂.obj i ⟶ F₁.obj (Order.succ i)`, then the
induced map between their colimits is an isomorphism
(`CategoryTheory.Limits.IsColimit.isIso_of_interleave`,
`CategoryTheory.Limits.IsColimit.isIso_map_of_interleave` and
`CategoryTheory.Limits.isIso_colimMap_of_interleave`).
-/

@[expose] public section

universe w u v

namespace CategoryTheory.Limits

variable {A : Type u} [Category.{v} A] {ι : Type w} [PartialOrder ι] [SuccOrder ι]
  {F₁ F₂ : ι ⥤ A}

namespace IsColimit

variable {c₁ : Cocone F₁} {c₂ : Cocone F₂}

/-- Let `F₁ F₂ : ι ⥤ A` be diagrams indexed by a partial order with a successor function, with
a natural transformation `u : F₁ ⟶ F₂` and maps `v i : F₂.obj i ⟶ F₁.obj (succ i)` interleaving
it with the transition maps:
```
F₁.obj i ──────▶ F₁.obj (succ i)
   │          ↗        │
 u.app i   v i   u.app (succ i)
   ▼      ╱            ▼
F₂.obj i ──────▶ F₂.obj (succ i)
```
i.e. `u.app i ≫ v i` and `v i ≫ u.app (succ i)` are the transition maps of `F₁` and `F₂`. Then
any map `f` between colimits of `F₁` and `F₂` compatible with `u` is an isomorphism. The inverse
is induced by the maps `v i`; no naturality of `v` in `i` is needed. -/
lemma isIso_of_interleave (h₁ : IsColimit c₁) (h₂ : IsColimit c₂)
    (u : F₁ ⟶ F₂) (v : ∀ i, F₂.obj i ⟶ F₁.obj (Order.succ i))
    (hu : ∀ i, u.app i ≫ v i = F₁.map (homOfLE (Order.le_succ i)))
    (hv : ∀ i, v i ≫ u.app (Order.succ i) = F₂.map (homOfLE (Order.le_succ i)))
    (f : c₁.pt ⟶ c₂.pt) (hf : ∀ i, c₁.ι.app i ≫ f = u.app i ≫ c₂.ι.app i) : IsIso f := by
  let g : c₂.pt ⟶ c₁.pt := h₂.desc
    { pt := c₁.pt
      ι :=
        { app i := v i ≫ c₁.ι.app (Order.succ i)
          naturality i j hij := by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
            obtain h | h := (leOfHom hij).eq_or_lt
            · subst h
              rw [Subsingleton.elim hij (𝟙 i), F₂.map_id, Category.id_comp]
            · rw [Subsingleton.elim hij
                  (homOfLE (Order.le_succ i) ≫ homOfLE (Order.succ_le_of_lt h)),
                F₂.map_comp, ← hv, Category.assoc, Category.assoc, ← u.naturality_assoc,
                reassoc_of% (hu j), c₁.w, c₁.w] } }
  refine ⟨g, h₁.hom_ext fun i ↦ ?_, h₂.hom_ext fun i ↦ ?_⟩
  · rw [reassoc_of% (hf i), h₂.fac, reassoc_of% (hu i), c₁.w, Category.comp_id]
  · rw [reassoc_of% (h₂.fac _ i), Category.assoc, hf, reassoc_of% (hv i), c₂.w,
      Category.comp_id]

/-- The map `h₁.map c₂ u` between colimits induced by a natural transformation `u : F₁ ⟶ F₂`
which is interleaved with the transition maps by maps `v i : F₂.obj i ⟶ F₁.obj (succ i)` is an
isomorphism. See `CategoryTheory.Limits.IsColimit.isIso_of_interleave`. -/
lemma isIso_map_of_interleave (h₁ : IsColimit c₁) (h₂ : IsColimit c₂)
    (u : F₁ ⟶ F₂) (v : ∀ i, F₂.obj i ⟶ F₁.obj (Order.succ i))
    (hu : ∀ i, u.app i ≫ v i = F₁.map (homOfLE (Order.le_succ i)))
    (hv : ∀ i, v i ≫ u.app (Order.succ i) = F₂.map (homOfLE (Order.le_succ i))) :
    IsIso (h₁.map c₂ u) :=
  isIso_of_interleave h₁ h₂ u v hu hv _ (h₁.ι_map c₂ u)


end IsColimit

/-- The map of colimits `colimMap u` induced by a natural transformation `u : F₁ ⟶ F₂`
which is interleaved with the transition maps by maps `v i : F₂.obj i ⟶ F₁.obj (succ i)` is an
isomorphism. See `CategoryTheory.Limits.IsColimit.isIso_of_interleave`. -/
lemma isIso_colimMap_of_interleave [HasColimit F₁] [HasColimit F₂]
    (u : F₁ ⟶ F₂) (v : ∀ i, F₂.obj i ⟶ F₁.obj (Order.succ i))
    (hu : ∀ i, u.app i ≫ v i = F₁.map (homOfLE (Order.le_succ i)))
    (hv : ∀ i, v i ≫ u.app (Order.succ i) = F₂.map (homOfLE (Order.le_succ i))) :
    IsIso (colimMap u) :=
  IsColimit.isIso_map_of_interleave (colimit.isColimit _) (colimit.isColimit _) u v hu hv


end CategoryTheory.Limits
