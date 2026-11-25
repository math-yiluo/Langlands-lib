/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.Triangle

/-!
# Towers of compactifications

For composable morphisms `f : X ⟶ Y`, `g : Y ⟶ S`, `h : S ⟶ T`, a *tower of compactifications*
consists of compactifications of `f`, `g`, `h`, `f ≫ g`, `g ≫ h`, `f ≫ g ≫ h` and maps between
their ambient schemes such that the four triangles of compactifications of `(f, g)`, `(g, h)`,
`(f, g ≫ h)` and `(f ≫ g, h)` share their compactifications:
```
cf.Z --q--> cfg.Z --q'--> cfgh.Z
 |cf.g        |p             |p₁
 Y ---cg.i--> cg.Z --q₂---> cgh.Z
                |cg.g          |p₂
                S ----ch.i---> ch.Z
```
with all squares cartesian. It is the configuration on which the associativity of the composition
isomorphism of `Rf_!` is a pasting identity (blueprint
`proposition-composition-base-change-rf-shriek--1`).

## Main definitions

- `AlgebraicGeometry.Compactification.Tower`: a tower of compactifications, with its triangles
  `Tower.fg`, `Tower.gh`, `Tower.f_gh` and `Tower.fg_h`.
- `AlgebraicGeometry.Compactification.Tower.ofHasCompactification`: a tower built from the chosen
  compactifications of `h`, `g ≫ h` and `f ≫ g ≫ h`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {X Y S T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S} {h : S ⟶ T}

variable (f g h) in
/-- **A tower of compactifications** of composable morphisms `f`, `g`, `h`. -/
structure Tower where
  /-- The compactification of `f`. -/
  cf : Compactification f
  /-- The compactification of `g`. -/
  cg : Compactification g
  /-- The compactification of `h`. -/
  ch : Compactification h
  /-- The compactification of `f ≫ g`. -/
  cfg : Compactification (f ≫ g)
  /-- The compactification of `g ≫ h`. -/
  cgh : Compactification (g ≫ h)
  /-- The compactification of `f ≫ g ≫ h`. -/
  cfgh : Compactification (f ≫ g ≫ h)
  /-- The open immersion `cf.Z ⟶ cfg.Z`. -/
  q : cf.Z ⟶ cfg.Z
  /-- The map `cfg.Z ⟶ cg.Z`. -/
  p : cfg.Z ⟶ cg.Z
  /-- The open immersion `cg.Z ⟶ cgh.Z`. -/
  q₂ : cg.Z ⟶ cgh.Z
  /-- The map `cgh.Z ⟶ ch.Z`. -/
  p₂ : cgh.Z ⟶ ch.Z
  /-- The open immersion `cfg.Z ⟶ cfgh.Z`. -/
  q' : cfg.Z ⟶ cfgh.Z
  /-- The map `cfgh.Z ⟶ cgh.Z`. -/
  p₁ : cfgh.Z ⟶ cgh.Z
  [isOpenImmersion_q : IsOpenImmersion q]
  [isOpenImmersion_q₂ : IsOpenImmersion q₂]
  [isOpenImmersion_q' : IsOpenImmersion q']
  i_q : cf.i ≫ q = cfg.i
  p_g : p ≫ cg.g = cfg.g
  isPullback_fg : IsPullback cf.g q cg.i p
  i_q₂ : cg.i ≫ q₂ = cgh.i
  p₂_g : p₂ ≫ ch.g = cgh.g
  isPullback_gh : IsPullback cg.g q₂ ch.i p₂
  i_q' : cfg.i ≫ q' = cfgh.i
  p₁_g : p₁ ≫ cgh.g = cfgh.g
  isPullback_mid : IsPullback p q' q₂ p₁

namespace Tower

attribute [instance] isOpenImmersion_q isOpenImmersion_q₂ isOpenImmersion_q'

variable (𝒯 : Tower f g h)

/-- The triangle of `(f, g)`. -/
@[simps]
abbrev fg : Triangle f g where
  cf := 𝒯.cf
  cg := 𝒯.cg
  cfg := 𝒯.cfg
  q := 𝒯.q
  p := 𝒯.p
  i_q := 𝒯.i_q
  p_g := 𝒯.p_g
  isPullback := 𝒯.isPullback_fg

/-- The triangle of `(g, h)`. -/
@[simps]
abbrev gh : Triangle g h where
  cf := 𝒯.cg
  cg := 𝒯.ch
  cfg := 𝒯.cgh
  q := 𝒯.q₂
  p := 𝒯.p₂
  i_q := 𝒯.i_q₂
  p_g := 𝒯.p₂_g
  isPullback := 𝒯.isPullback_gh

/-- The triangle of `(f, g ≫ h)`. -/
@[simps]
abbrev f_gh : Triangle f (g ≫ h) where
  cf := 𝒯.cf
  cg := 𝒯.cgh
  cfg := 𝒯.cfgh
  q := 𝒯.q ≫ 𝒯.q'
  p := 𝒯.p₁
  i_q := by rw [reassoc_of% 𝒯.i_q, 𝒯.i_q']
  p_g := 𝒯.p₁_g
  isPullback := by
    have := 𝒯.isPullback_fg.paste_vert 𝒯.isPullback_mid
    rwa [𝒯.i_q₂] at this

/-- The triangle of `(f ≫ g, h)`. -/
@[simps]
abbrev fg_h : Triangle (f ≫ g) h where
  cf := 𝒯.cfg
  cg := 𝒯.ch
  cfg :=
    { Z := 𝒯.cfgh.Z
      g := 𝒯.cfgh.g
      i := 𝒯.cfgh.i
      comm := (Category.assoc f g h).trans 𝒯.cfgh.comm
      isProper := 𝒯.cfgh.isProper
      isOpenImmersion := 𝒯.cfgh.isOpenImmersion }
  q := 𝒯.q'
  p := 𝒯.p₁ ≫ 𝒯.p₂
  i_q := 𝒯.i_q'
  p_g := (Category.assoc _ _ _).trans ((congrArg (𝒯.p₁ ≫ ·) 𝒯.p₂_g).trans 𝒯.p₁_g)
  isPullback := by
    have := 𝒯.isPullback_mid.paste_horiz 𝒯.isPullback_gh
    rwa [𝒯.p_g] at this


section OfHasCompactification

variable (f g h) [HasCompactification h] [HasCompactification (g ≫ h)]
  [HasCompactification (f ≫ g ≫ h)] [QuasiCompact (g ≫ h)] [QuasiCompact (f ≫ g ≫ h)]

/-- The compactification of `g ≫ ch.i` underlying `Tower.ofHasCompactification`. -/
noncomputable abbrev towerE₂ : Compactification (g ≫ (HasCompactification.compactification h).i) :=
  (HasCompactification.compactification (g ≫ h)).ofComp _

/-- The compactification of `f ≫ e₂.i` underlying `Tower.ofHasCompactification`. -/
noncomputable abbrev towerE₁ : Compactification (f ≫ (towerE₂ g h).i) :=
  (HasCompactification.compactification (f ≫ g ≫ h)).ofComp
    ((HasCompactification.compactification h).comp (towerE₂ g h))

/-- The compactification of `(f ≫ g) ≫ ch.i` underlying `Tower.ofHasCompactification`. -/
noncomputable abbrev towerE :
    Compactification ((f ≫ g) ≫ (HasCompactification.compactification h).i) :=
  ((towerE₂ g h).comp (towerE₁ f g h)).copy (Category.assoc _ _ _)

/-- The open immersion `cf.Z ⟶ cfg.Z` underlying `Tower.ofHasCompactification`. -/
noncomputable abbrev towerQ : (towerE₁ f g h).restrict.Z ⟶ (towerE f g h).restrict.Z :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g) (by
    change pullback.fst _ _ ≫ (towerE₁ f g h).g ≫ (towerE₂ g h).g = _
    rw [pullback.condition_assoc, Category.assoc]
    exact congrArg (pullback.snd _ _ ≫ ·) (towerE₂ g h).comm.symm)

/-- The map `cfg.Z ⟶ cg.Z` underlying `Tower.ofHasCompactification`. -/
noncomputable abbrev towerP : (towerE f g h).restrict.Z ⟶ (towerE₂ g h).restrict.Z :=
  pullback.lift (pullback.fst _ _ ≫ (towerE₁ f g h).g) (pullback.snd _ _) (by
    rw [Category.assoc]
    exact pullback.condition)

lemma towerQ_fst : towerQ f g h ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

instance : IsOpenImmersion (towerQ f g h) :=
  have : IsOpenImmersion (towerQ f g h ≫ pullback.fst _ _) := by
    rw [towerQ_fst]; infer_instance
  .of_comp _ (pullback.fst (towerE f g h).g (HasCompactification.compactification h).i)

lemma isPullback_towerMid : IsPullback (towerP f g h) (pullback.fst _ _) (pullback.fst _ _)
    (towerE₁ f g h).g := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (towerE₂ g h).isPullback_restrict
  rw [show towerP f g h ≫ (towerE₂ g h).restrict.g = (towerE f g h).restrict.g from
    pullback.lift_snd _ _ _]
  exact (towerE f g h).isPullback_restrict

lemma towerE₁_restrict_g_i : (towerE₁ f g h).restrict.g ≫ (towerE₂ g h).restrict.i =
    towerQ f g h ≫ towerP f g h := by
  apply pullback.hom_ext
  · rw [Category.assoc, restrict_i_fst, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
      restrict_g, ← pullback.condition]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd, restrict_g]
    have := (towerE₂ g h).restrict.comm
    exact congrArg (pullback.snd _ _ ≫ ·) this.symm

/-- **A tower of compactifications** built from the chosen compactifications of `h`, `g ≫ h` and
`f ≫ g ≫ h`. -/
noncomputable def ofHasCompactification : Tower f g h where
  cf := (towerE₁ f g h).restrict
  cg := (towerE₂ g h).restrict
  ch := HasCompactification.compactification h
  cfg := (towerE f g h).restrict
  cgh := (HasCompactification.compactification h).comp (towerE₂ g h)
  cfgh := ((HasCompactification.compactification h).comp (towerE₂ g h)).comp (towerE₁ f g h)
  q := towerQ f g h
  p := towerP f g h
  q₂ := pullback.fst _ _
  p₂ := (towerE₂ g h).g
  q' := pullback.fst _ _
  p₁ := (towerE₁ f g h).g
  i_q := by
    apply pullback.hom_ext
    · rw [Category.assoc (towerE₁ f g h).restrict.i (towerQ f g h), towerQ_fst, restrict_i_fst,
        restrict_i_fst]
      rfl
    · rw [Category.assoc (towerE₁ f g h).restrict.i (towerQ f g h), pullback.lift_snd,
        ← Category.assoc]
      have h₁ := (towerE₁ f g h).restrict.comm
      have h₂ := (towerE f g h).restrict.comm
      rw [restrict_g] at h₁ h₂
      rw [← h₁, ← h₂]
  p_g := pullback.lift_snd _ _ _
  isPullback_fg := by
    refine IsPullback.of_bot ?_ (towerE₁_restrict_g_i f g h) (isPullback_towerMid f g h)
    rw [towerQ_fst, restrict_i_fst]
    exact (towerE₁ f g h).isPullback_restrict
  i_q₂ := (towerE₂ g h).restrict_i_fst
  p₂_g := rfl
  isPullback_gh := (towerE₂ g h).isPullback_restrict
  i_q' := (towerE f g h).restrict_i_fst
  p₁_g := rfl
  isPullback_mid := isPullback_towerMid f g h

end OfHasCompactification

end Tower

end AlgebraicGeometry.Compactification
