/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# The triple fibre product as a base change of its outer projection

Let `X ×_S Y ×_S Z` be realised as `(X ×_S Y) ×_Y (Y ×_S Z)`, with outer projection
`r₁₃ : X ×_S Y ×_S Z ⟶ X ×_S Z`. For any morphism `m : X ×_S Z ⟶ W` over `X`-composed-with-`S`
(that is, `m ≫ k = p₁ ≫ f` for some `k : W ⟶ S`), the square

```
  X ×ₛ Y ×ₛ Z ──(r₁₂ ≫ p₂, r₁₃ ≫ m)──▶ Y ×ₛ W
        │                                  │
     r₁₃│                                  │q₂
        ▼                                  ▼
     X ×ₛ Z ─────────────m───────────────▶ W
```

is cartesian: both sides are `(X ×_S Z) ×_S Y`. On points this is the change of variables
`(x, y, z) ↦ (y, m(x, z))`.

## Main definitions

- `CategoryTheory.Limits.pullback.tripleShear`: the morphism `(x, y, z) ↦ (y, m(x, z))`.

## Main statements

- `CategoryTheory.Limits.pullback.isPullback_tripleShear_tripleProj₁₃`: the square above is
  cartesian.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {S X Y Z W : C} (f : X ⟶ S) (g : Y ⟶ S)
  (h : Z ⟶ S) {m : pullback f h ⟶ W} {k : W ⟶ S}

/-- The morphism `(x, y, z) ↦ (y, m(x, z))` from the triple fibre product
`(X ×_S Y) ×_Y (Y ×_S Z)` to `Y ×_S W`, for `m : X ×_S Z ⟶ W` with `m ≫ k = p₁ ≫ f`. -/
noncomputable def pullback.tripleShear (hm : m ≫ k = pullback.fst f h ≫ f) :
    pullback (pullback.snd f g) (pullback.fst g h) ⟶ pullback g k :=
  pullback.lift (pullback.fst _ _ ≫ pullback.snd f g) (pullback.tripleProj₁₃ f g h ≫ m) (by
    rw [Category.assoc, Category.assoc, hm, pullback.tripleProj₁₃_fst_assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma pullback.tripleShear_fst (hm : m ≫ k = pullback.fst f h ≫ f) :
    pullback.tripleShear f g h hm ≫ pullback.fst g k = pullback.fst _ _ ≫ pullback.snd f g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullback.tripleShear_snd (hm : m ≫ k = pullback.fst f h ≫ f) :
    pullback.tripleShear f g h hm ≫ pullback.snd g k = pullback.tripleProj₁₃ f g h ≫ m :=
  pullback.lift_snd _ _ _

/-- The triple fibre product `X ×_S Y ×_S Z` is the base change of `q₂ : Y ×_S W ⟶ W` along
`m : X ×_S Z ⟶ W`, through `r₁₃` and the shear `(x, y, z) ↦ (y, m(x, z))`. -/
theorem pullback.isPullback_tripleShear_tripleProj₁₃ (hm : m ≫ k = pullback.fst f h ≫ f) :
    IsPullback (pullback.tripleShear f g h hm) (pullback.tripleProj₁₃ f g h)
      (pullback.snd g k) m := by
  have c₁ (s : PullbackCone (pullback.snd g k) m) :
      (s.snd ≫ pullback.fst f h) ≫ f = (s.fst ≫ pullback.fst g k) ≫ g := by
    rw [Category.assoc, Category.assoc, pullback.condition (f := g), ← hm,
      PullbackCone.condition_assoc]
  have c₂ (s : PullbackCone (pullback.snd g k) m) :
      (s.fst ≫ pullback.fst g k) ≫ g = (s.snd ≫ pullback.snd f h) ≫ h := by
    rw [← c₁, Category.assoc, Category.assoc, pullback.condition]
  refine ⟨⟨pullback.tripleShear_snd f g h hm⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s ↦ pullback.lift (pullback.lift _ _ (c₁ s)) (pullback.lift _ _ (c₂ s))
      (by rw [pullback.lift_snd, pullback.lift_fst]))
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s l hl₁ hl₂ ↦ ?_)⟩⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.tripleShear_fst, pullback.lift_fst_assoc, pullback.lift_snd]
    · rw [Category.assoc, pullback.tripleShear_snd, ← Category.assoc, s.condition]
      congr 1
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, pullback.tripleProj₁₃_fst, pullback.lift_fst_assoc,
          pullback.lift_fst]
      · rw [Category.assoc, pullback.tripleProj₁₃_snd, pullback.lift_snd_assoc,
          pullback.lift_snd]
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.tripleProj₁₃_fst, pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc, pullback.tripleProj₁₃_snd, pullback.lift_snd_assoc, pullback.lift_snd]
  · refine pullback.hom_ext (pullback.hom_ext ?_ ?_) (pullback.hom_ext ?_ ?_)
    · simp only [Category.assoc, pullback.lift_fst, ← hl₂,
        pullback.tripleProj₁₃_fst]
    · simp only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, ← hl₁,
        pullback.tripleShear_fst]
    · simp only [Category.assoc, pullback.lift_snd_assoc, pullback.lift_fst, ← hl₁,
        pullback.tripleShear_fst, pullback.condition]
    · simp only [Category.assoc, pullback.lift_snd, ← hl₂,
        pullback.tripleProj₁₃_snd]

end CategoryTheory.Limits
