/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.Triangle

/-!
# Base change of a triangle of compactifications

Let `T` be a triangle of compactifications of composable morphisms `f : X ⟶ Y`, `g : Y ⟶ S`, and
let
```
X' --gX--> X
|f'        |f
Y' --gY--> Y
|g'        |g
S' --gS--> S
```
be two cartesian squares (with cartesian outer rectangle). The base changes
`T.cf.ofIsPullback sq₁`, `T.cg.ofIsPullback sq₂` and `T.cfg.ofIsPullback sq` of the three
compactifications form a triangle of compactifications `T.ofIsPullback sq₁ sq₂ sq` of `(f', g')`,
whose maps `q` and `p` are the base changes of those of `T`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification.Triangle

variable {X Y S X' Y' S' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S} {f' : X' ⟶ Y'} {g' : Y' ⟶ S'}
  {gX : X' ⟶ X} {gY : Y' ⟶ Y} {gS : S' ⟶ S} (T : Triangle f g)

@[reassoc]
lemma q_cfg_g : T.q ≫ T.cfg.g = T.cf.g ≫ g := by
  rw [← T.p_g, ← reassoc_of% T.isPullback.w, ← T.cg.comm]

/-- The base change `T.cf.Z ×_Y Y' ⟶ T.cfg.Z ×_S S'` of the open immersion `T.q`. -/
noncomputable def baseChangeQ (sq₂ : IsPullback gY g' g gS) :
    pullback T.cf.g gY ⟶ pullback T.cfg.g gS :=
  pullback.lift (pullback.fst _ _ ≫ T.q) (pullback.snd _ _ ≫ g') (by
    rw [Category.assoc, q_cfg_g, pullback.condition_assoc, Category.assoc, sq₂.w])

@[reassoc (attr := simp)]
lemma baseChangeQ_fst (sq₂ : IsPullback gY g' g gS) :
    T.baseChangeQ sq₂ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ T.q :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeQ_snd (sq₂ : IsPullback gY g' g gS) :
    T.baseChangeQ sq₂ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ g' :=
  pullback.lift_snd _ _ _

/-- The base change `T.cfg.Z ×_S S' ⟶ T.cg.Z ×_S S'` of the proper map `T.p`. -/
noncomputable def baseChangeP : pullback T.cfg.g gS ⟶ pullback T.cg.g gS :=
  pullback.map _ _ _ _ T.p (𝟙 _) (𝟙 _) (by rw [T.p_g, Category.comp_id]) (by simp)

@[reassoc (attr := simp)]
lemma baseChangeP_fst : T.baseChangeP (gS := gS) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ T.p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma baseChangeP_snd :
    T.baseChangeP (gS := gS) ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp [baseChangeP]

/-- The square of the base change of `T.q` is cartesian. -/
theorem isPullback_baseChangeQ (sq₂ : IsPullback gY g' g gS) :
    IsPullback (pullback.fst T.cf.g gY) (T.baseChangeQ sq₂) T.q (pullback.fst T.cfg.g gS) := by
  refine IsPullback.of_bot ?_ (T.baseChangeQ_fst sq₂).symm (IsPullback.of_hasPullback T.cfg.g gS)
  rw [baseChangeQ_snd, q_cfg_g]
  exact (IsPullback.of_hasPullback T.cf.g gY).paste_vert sq₂

/-- The square of the base change of `T.p` is cartesian. -/
theorem isPullback_baseChangeP :
    IsPullback (pullback.fst T.cfg.g gS) T.baseChangeP T.p (pullback.fst T.cg.g gS) := by
  refine IsPullback.of_bot ?_ T.baseChangeP_fst.symm (IsPullback.of_hasPullback T.cg.g gS)
  rw [baseChangeP_snd, T.p_g]
  exact IsPullback.of_hasPullback T.cfg.g gS

/-- **Base change of a triangle of compactifications** along cartesian squares
`sq₁ : IsPullback gX f' f gY`, `sq₂ : IsPullback gY g' g gS` and
`sq : IsPullback gX (f' ≫ g') (f ≫ g) gS`: the triangle formed by the base changes of the three
compactifications of `T`. -/
@[simps]
noncomputable def ofIsPullback (sq₁ : IsPullback gX f' f gY) (sq₂ : IsPullback gY g' g gS)
    (sq : IsPullback gX (f' ≫ g') (f ≫ g) gS) : Triangle f' g' where
  cf := T.cf.ofIsPullback sq₁
  cg := T.cg.ofIsPullback sq₂
  cfg := T.cfg.ofIsPullback sq
  q := T.baseChangeQ sq₂
  p := T.baseChangeP
  isOpenImmersion_q := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (T.isPullback_baseChangeQ sq₂) inferInstance
  i_q := pullback.hom_ext (by simp [T.i_q]) (by simp)
  p_g := by simp
  isPullback := by
    refine (IsPullback.of_right ?_ ?_ T.isPullback_baseChangeP).flip
    · rw [baseChangeQ_fst, ofIsPullback_i_fst]
      exact (IsPullback.of_hasPullback T.cf.g gY).paste_horiz T.isPullback.flip
    · apply pullback.hom_ext
      · simp only [ofIsPullback_g, Category.assoc, baseChangeP_fst,
          baseChangeQ_fst_assoc, ofIsPullback_i_fst]
        rw [← T.isPullback.w, pullback.condition_assoc]
      · simp

end AlgebraicGeometry.Compactification.Triangle
