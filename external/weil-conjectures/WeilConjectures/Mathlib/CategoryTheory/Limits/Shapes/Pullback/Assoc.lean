/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc

/-!
# The triple fibre product and its outer projection

For three objects `X`, `Y`, `Z` over a common base `S`, the triple fibre product
`X ×_S Y ×_S Z` may be realised as `(X ×_S Y) ×_Y (Y ×_S Z)`. The two projections of that
fibre product are the partial projections `r₁₂` and `r₂₃`; this file constructs the
remaining one,

- `CategoryTheory.Limits.pullback.tripleProj₁₃`.

-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {S X Y Z : C} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  [HasPullback f g] [HasPullback g h] [HasPullback f h]
  [HasPullback (pullback.snd f g) (pullback.fst g h)]

/-- The outer projection `r₁₃ : X ×_S Y ×_S Z ⟶ X ×_S Z` of the triple fibre product,
the latter realised as `(X ×_S Y) ×_Y (Y ×_S Z)`:

```
  (X ×ₛ Y) ×_Y (Y ×ₛ Z) --- r₁₂ ---▶ X ×ₛ Y --- p₁ ---▶ X
            │                           │               │
          r₂₃│                          │p₂             │f
            ▼                           ▼               ▼
        Y ×ₛ Z --- q₁ ---▶             Y --- g ---▶     S
            │
          q₂│
            ▼
            Z
```

`r₁₂` and `r₂₃` are the two projections of `(X ×_S Y) ×_Y (Y ×_S Z)`, and `r₁₃` is the
morphism to `X ×_S Z` with components `r₁₂ ≫ p₁` and `r₂₃ ≫ q₂`. -/
noncomputable def pullback.tripleProj₁₃ :
    pullback (pullback.snd f g) (pullback.fst g h) ⟶ pullback f h :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f g) (pullback.snd _ _ ≫ pullback.snd g h)
    (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
      Category.assoc, pullback.condition, Category.assoc])

@[reassoc (attr := simp)]
lemma pullback.tripleProj₁₃_fst :
    pullback.tripleProj₁₃ f g h ≫ pullback.fst f h =
      pullback.fst _ _ ≫ pullback.fst f g :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullback.tripleProj₁₃_snd :
    pullback.tripleProj₁₃ f g h ≫ pullback.snd f h =
      pullback.snd _ _ ≫ pullback.snd g h :=
  pullback.lift_snd _ _ _

end CategoryTheory.Limits
