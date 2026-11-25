/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import Mathlib.CategoryTheory.Functor.TwoSquare

/-!
# Conjugating vertical composites of 2-squares

For 2-squares `a : TwoSquare T L R B` and `b : TwoSquare B L' R'' B''` and isomorphisms
`e : B ≅ Bt`, `e'' : B'' ≅ Bt''`, the vertical composite of the conjugated squares
`a ≫ L e` and `R'' e⁻¹ ≫ b ≫ L' e''` is the conjugate of the vertical composite of `a` and `b`
(`CategoryTheory.TwoSquare.vComp_conj`), also after whiskering
(`CategoryTheory.TwoSquare.whiskerLeft_whiskerRight_vComp_conj`).
-/

@[expose] public section

namespace CategoryTheory.TwoSquare

open CategoryTheory.Functor

variable {C₁ C₂ C₃ C₄ C₇ C₈ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* C₇] [Category* C₈]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B Bt : C₃ ⥤ C₄} {L' : C₃ ⥤ C₇}
  {R'' : C₄ ⥤ C₈} {B'' Bt'' : C₇ ⥤ C₈}

/-- The vertical composite of conjugated 2-squares is the conjugated vertical composite: for the
2-squares `a` and `b` stacked vertically and isomorphisms `e : B ≅ Bt`, `e'' : B'' ≅ Bt''`
```
C₁ --T---> C₂
|L    a    |R
v          v
C₃ --B---> C₄        e : B ≅ Bt
|L'   b    |R''
v          v
C₇ --B''-> C₈        e'' : B'' ≅ Bt''
```
replacing `B` by `Bt` in both squares (through `e`) and `B''` by `Bt''` (through `e''`) and
composing vertically gives the vertical composite of `a` and `b` followed by `e''`. -/
lemma vComp_conj (a : TwoSquare T L R B) (b : TwoSquare B L' R'' B'') (e : B ≅ Bt)
    (e'' : B'' ≅ Bt'') :
    TwoSquare.vComp (T := T) (B := Bt) (a ≫ whiskerLeft L e.hom)
        (whiskerRight e.inv R'' ≫ b ≫ whiskerLeft L' e''.hom) =
      (TwoSquare.vComp a b) ≫ whiskerLeft (L ⋙ L') e''.hom := by
  ext X
  simp [vComp, ← Functor.map_comp_assoc]

variable {L'' : C₁ ⥤ C₇} {R''' : C₂ ⥤ C₈}

/-- The vertical composite of conjugated 2-squares, whiskered on the left and on the right, is
the conjugate of the whiskered vertical composite: for the 2-squares `a` and `b` stacked as in
`CategoryTheory.TwoSquare.vComp_conj`
```
C₁ --T---> C₂
|L    a    |R
v          v
C₃ --B---> C₄        e : B ≅ Bt
|L'   b    |R''
v          v
C₇ --B''-> C₈        e'' : B'' ≅ Bt''
```
and natural transformations `α : L ⋙ L' ⟶ L''`, `β : R''' ⟶ R ⋙ R''`, a 2-square `s` from `T` to
`B''` with sides `L''` and `R'''` equal to the whiskered vertical composite of `a` and `b`, followed
by `e''`, is the whiskered vertical composite of the conjugated squares. -/
lemma whiskerLeft_whiskerRight_vComp_conj (a : TwoSquare T L R B) (b : TwoSquare B L' R'' B'')
    (e : B ≅ Bt) (e'' : B'' ≅ Bt'') (α : L ⋙ L' ⟶ L'') (β : R''' ⟶ R ⋙ R'')
    (s : TwoSquare T L'' R''' B'') (hs : s = ((TwoSquare.vComp a b).whiskerLeft α).whiskerRight β) :
    s ≫ whiskerLeft L'' e''.hom =
      ((TwoSquare.vComp (T := T) (B := Bt) (a ≫ whiskerLeft L e.hom)
        (whiskerRight e.inv R'' ≫ b ≫ whiskerLeft L' e''.hom)).whiskerLeft
          α).whiskerRight β := by
  subst hs
  rw [vComp_conj]
  ext X
  simp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight]

end CategoryTheory.TwoSquare
