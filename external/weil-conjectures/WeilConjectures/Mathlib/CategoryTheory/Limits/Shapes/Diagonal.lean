/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Equalizers as pullbacks of the diagonal

For two morphisms `f g : T ⟶ X` over `S`, the equalizer of `f` and `g` is the pullback of
`(f, g) : C ⟶ X ×_S X` along the diagonal of `X ⟶ S`:

- `CategoryTheory.Limits.isPullback_equalizer_ι_diagonal`.

We also record that the diagonal is compatible with restriction along monomorphisms:

- `CategoryTheory.Limits.isPullback_diagonal_map_of_mono`.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {T X S : C} {p : X ⟶ S} [HasPullback p p]
  (f g : T ⟶ X) [HasEqualizer f g] (h : f ≫ p = g ≫ p)

/-- The equalizer of `f g : T ⟶ X` over `S` is the pullback of `(f, g) : T ⟶ X ×_S X` along
the diagonal:

```
  equalizer f g ──ι──▶ T
        │              │
     ι ≫ f             │ (f, g)
        ▼              ▼
        X ─────Δ─────▶ X ×_S X
```

is Cartesian. -/
lemma isPullback_equalizer_ι_diagonal :
    IsPullback (equalizer.ι f g) (equalizer.ι f g ≫ f) (pullback.lift f g h)
      (pullback.diagonal p) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (by apply pullback.hom_ext <;> simp [equalizer.condition f g])
    (fun t ↦ equalizer.lift t.fst ?_)
    (fun t ↦ equalizer.lift_ι _ _) (fun t ↦ ?_)
    (fun t m h₁ _ ↦ equalizer.hom_ext (by simpa using h₁)))
  all_goals
    have h₁ := t.condition =≫ pullback.fst p p
    have h₂ := t.condition =≫ pullback.snd p p
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd] at h₁ h₂
  · rw [h₁, h₂]
  · simp [h₁]

section

variable {X Y X' Y' : C} {f : X ⟶ Y} {f' : X' ⟶ Y'} [HasPullback f f] [HasPullback f' f']

/-- The diagonal is compatible with restriction along a monomorphism: for `i : X' ⟶ X` a
monomorphism and a commutative square `f' ≫ j = i ≫ f`, the square

```
  X' ───Δ_{f'}───▶ X' ×_{Y'} X'
  │                    │
  i                    │ i × i
  ▼                    ▼
  X ─────Δ_f─────▶  X ×_Y X
```

is Cartesian. -/
lemma isPullback_diagonal_map_of_mono (i : X' ⟶ X) (j : Y' ⟶ Y) [Mono i] (h : f' ≫ j = i ≫ f) :
    IsPullback i (pullback.diagonal f') (pullback.diagonal f)
      (pullback.map f' f' f f i i j h h) := by
  have key (t : PullbackCone (pullback.diagonal f) (pullback.map f' f' f f i i j h h)) :
      (t.snd ≫ pullback.fst f' f') ≫ i = t.fst ∧
        t.snd ≫ pullback.fst f' f' = t.snd ≫ pullback.snd f' f' := by
    have h₁ := t.condition =≫ pullback.fst f f
    have h₂ := t.condition =≫ pullback.snd f f
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd, Category.comp_id] at h₁ h₂
    refine ⟨by rw [Category.assoc, h₁], ?_⟩
    rw [← cancel_mono i, Category.assoc, Category.assoc, ← h₁, ← h₂]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (by ext <;> simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
      Category.comp_id, limit.isLimit_lift, limit.lift_π, PullbackCone.mk_π_app,
      limit.lift_π_assoc, cospan_left, cospan_right] <;> exact (Category.id_comp i).symm)
    (fun t ↦ t.snd ≫ pullback.fst f' f') (fun t ↦ (key t).1)
    (fun t ↦ by ext <;> simp [(key t).2])
    (fun t m h₁ _ ↦ by rw [← cancel_mono i, h₁, (key t).1]))

end

end CategoryTheory.Limits
