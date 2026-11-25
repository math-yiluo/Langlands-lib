/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Postcomposing a transformation of bifunctors

Given a natural transformation `τ` of bifunctors and a functor `Q`, we define
`postcompose₂MapWhiskeringLeft₂ τ Q`, the postcomposition of `τ` with `Q`.

## Implementation notes

`postcompose₂MapWhiskeringLeft₂ τ Q` is definitionally `(postcompose₂.obj Q).map τ`; only its
source and target are written differently, as `postcompose₂.obj (F ⋙ Q)` and
`whiskeringLeft₂ F₁ F₂ ∘ postcompose₂.obj Q`. When `F`, `Q`, `F₁` and `F₂` are concrete functors,
the kernel can take minutes to check these definitional equalities, e.g. matching
`postcompose₂ (F ⋙ Q)` against `postcompose₂ Q ∘ postcompose₂ F`. Stating them once, for
abstract functors, avoids this. For the same reason, the file also states the evaluation of a
whiskering on both sides, `CategoryTheory.Functor.whiskerLeft_whiskerRight_app`.

-/

@[expose] public section

namespace CategoryTheory.Functor

variable {C₁ C₂ D₁ D₂ E E' E'' : Type*} [Category* C₁] [Category* C₂] [Category* D₁]
  [Category* D₂] [Category* E] [Category* E'] [Category* E'']
  {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {G : C₁ ⥤ C₂ ⥤ E} {F : E ⥤ E'} {B : D₁ ⥤ D₂ ⥤ E'}
  (τ : (postcompose₂.obj F).obj G ⟶ (((whiskeringLeft₂ E').obj F₁).obj F₂).obj B)
  (Q : E' ⥤ E'')

/-- The postcomposition of a natural transformation `τ` of bifunctors with a functor `Q`:
```
  Q ∘ F ∘ G ──Q τ──▶ Q ∘ B ∘ (F₁ × F₂)
```
-/
@[simps!]
def postcompose₂MapWhiskeringLeft₂ :
    (postcompose₂.obj (F ⋙ Q)).obj G ⟶
      (((whiskeringLeft₂ E'').obj F₁).obj F₂).obj ((postcompose₂.obj Q).obj B) :=
  (postcompose₂.obj Q).map τ

instance isIso_postcompose₂MapWhiskeringLeft₂ [IsIso τ] :
    IsIso (postcompose₂MapWhiskeringLeft₂ τ Q) :=
  Functor.map_isIso (postcompose₂.obj Q) τ

end CategoryTheory.Functor

namespace CategoryTheory.Functor

/-- Whiskering on both sides, evaluated at an object. -/
lemma whiskerLeft_whiskerRight_app
    {𝒜 ℬ 𝒞 𝒟 : Type*} [Category* 𝒜] [Category* ℬ]
    [Category* 𝒞] [Category* 𝒟] (E : 𝒜 ⥤ ℬ) {P Q : ℬ ⥤ 𝒞} (α : P ⟶ Q) (Hh : 𝒞 ⥤ 𝒟) (X : 𝒜) :
    (Functor.whiskerLeft E (Functor.whiskerRight α Hh)).app X = Hh.map (α.app (E.obj X)) :=
  rfl

end CategoryTheory.Functor
