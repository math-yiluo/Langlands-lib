/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.Comp
public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Compactification.Constructions
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Compactification.RefinementPullback

/-!
# Triangles of compactifications

For composable morphisms `f : X ⟶ Y` and `g : Y ⟶ S`, a *triangle of compactifications* consists
of compactifications `cf`, `cg`, `cfg` of `f`, `g`, `f ≫ g`, together with an open immersion
`q : cf.Z ⟶ cfg.Z` and a morphism `p : cfg.Z ⟶ cg.Z` such that `cf.i ≫ q = cfg.i`,
`p ≫ cg.g = cfg.g` and the square
```
cf.Z --cf.g--> Y
 |q            |cg.i
cfg.Z ---p---> cg.Z
```
is cartesian. This is the configuration on which the composition isomorphism
`R(f ≫ g)_! ≅ Rf_! ⋙ Rg_!` is built (blueprint `proposition-composition-base-change-rf-shriek--1`):
extension by zero along `cg.i` commutes with the proper pushforward along `p`.

## Main definitions

- `AlgebraicGeometry.Compactification.Triangle`: a triangle of compactifications.
- `AlgebraicGeometry.Compactification.Triangle.ofRestrict`: the triangle attached to a
  compactification `d` of `g` and a compactification `e` of `f ≫ d.i`.
- `AlgebraicGeometry.Compactification.Triangle.Hom`: a morphism of triangles, i.e. compatible
  refinements of the three compactifications with cartesian squares.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}

variable (f g) in
/-- **A triangle of compactifications** of composable morphisms `f : X ⟶ Y`, `g : Y ⟶ S`:
compactifications `cf`, `cg`, `cfg` of `f`, `g`, `f ≫ g` and maps `q : cf.Z ⟶ cfg.Z` (an open
immersion) and `p : cfg.Z ⟶ cg.Z` with `cf.i ≫ q = cfg.i`, `p ≫ cg.g = cfg.g`, such that the
square `cf.g ≫ cg.i = q ≫ p` is cartesian. -/
structure Triangle where
  /-- The compactification of `f`. -/
  cf : Compactification f
  /-- The compactification of `g`. -/
  cg : Compactification g
  /-- The compactification of `f ≫ g`. -/
  cfg : Compactification (f ≫ g)
  /-- The open immersion `cf.Z ⟶ cfg.Z`. -/
  q : cf.Z ⟶ cfg.Z
  /-- The proper map `cfg.Z ⟶ cg.Z`. -/
  p : cfg.Z ⟶ cg.Z
  [isOpenImmersion_q : IsOpenImmersion q]
  i_q : cf.i ≫ q = cfg.i
  p_g : p ≫ cg.g = cfg.g
  isPullback : IsPullback cf.g q cg.i p

namespace Triangle

attribute [instance] isOpenImmersion_q

variable (T : Triangle f g)

instance isProper_p : IsProper T.p :=
  have : IsProper (T.p ≫ T.cg.g) := by rw [T.p_g]; infer_instance
  .of_comp T.p T.cg.g

/-- The triangle of compactifications attached to a compactification `d` of `g` and a
compactification `e` of `f ≫ d.i`: the compactifications `e.restrict` of `f`, `d` of `g` and
`d.comp e` of `f ≫ g`. -/
@[simps]
noncomputable def ofRestrict (d : Compactification g) (e : Compactification (f ≫ d.i)) :
    Triangle f g where
  cf := e.restrict
  cg := d
  cfg := d.comp e
  q := pullback.fst e.g d.i
  p := e.g
  i_q := e.restrict_i_fst
  p_g := rfl
  isPullback := e.isPullback_restrict

/-- **A morphism of triangles** `T' ⟶ T`: refinements of the three compactifications of `T` by
those of `T'`, compatible with `q` and `p`, whose squares over `X` and `Y` are cartesian. -/
structure Hom (T' T : Triangle f g) where
  /-- The refinement of the compactifications of `f`. -/
  rf : T'.cf.Refinement T.cf
  /-- The refinement of the compactifications of `g`. -/
  rg : T'.cg.Refinement T.cg
  /-- The refinement of the compactifications of `f ≫ g`. -/
  rfg : T'.cfg.Refinement T.cfg
  q_comm : rf.hom ≫ T.q = T'.q ≫ rfg.hom
  p_comm : T'.p ≫ rg.hom = rfg.hom ≫ T.p
  isPullback_rf : IsPullback T'.cf.i (𝟙 X) rf.hom T.cf.i
  isPullback_rg : IsPullback T'.cg.i (𝟙 Y) rg.hom T.cg.i

namespace Hom

variable {T' T : Triangle f g} (φ : T'.Hom T)

/-- The square `T'.cf.g ≫ T.cg.i = T'.q ≫ (T'.p ≫ φ.rg.hom)` is cartesian. -/
theorem isPullback_big : IsPullback T'.cf.g T'.q T.cg.i (T'.p ≫ φ.rg.hom) := by
  simpa using T'.isPullback.paste_horiz φ.isPullback_rg.flip

/-- The square `φ.rf.hom ≫ T.q = T'.q ≫ φ.rfg.hom` is cartesian. -/
theorem isPullback_q : IsPullback φ.rf.hom T'.q T.q φ.rfg.hom := by
  refine IsPullback.of_right (h₁₂ := T.cf.g) (h₂₂ := T.p) ?_ φ.q_comm T.isPullback
  rw [φ.rf.hom_g, ← φ.p_comm]
  exact φ.isPullback_big

/-- The square of the refinement of the compactifications of `f ≫ g` is cartesian. -/
theorem isPullback_rfg : IsPullback T'.cfg.i (𝟙 X) φ.rfg.hom T.cfg.i := by
  have := φ.isPullback_rf.flip.paste_vert φ.isPullback_q
  rw [T'.i_q, T.i_q] at this
  exact this.flip

end Hom

lemma cfg_i_p : T.cfg.i ≫ T.p = f ≫ T.cg.i := by
  rw [← T.i_q, Category.assoc, ← T.isPullback.w, ← Category.assoc, ← T.cf.comm]

section HomOfRestrict

variable (d : Compactification g) (rg : d.Refinement T.cg)
  (hrg : IsPullback d.i (𝟙 Y) rg.hom T.cg.i) (e : Compactification (f ≫ d.i))
  (m : e.Z ⟶ T.cfg.Z) (hm : e.i ≫ m = T.cfg.i) (hm' : e.g ≫ rg.hom = m ≫ T.p)

include hm hm' in
/-- The refinement of the compactifications of `f ≫ g` underlying `Triangle.homOfRestrict`. -/
@[simps]
def homOfRestrictRfg : (ofRestrict d e).cfg.Refinement T.cfg where
  hom := m
  i_hom := hm
  hom_g := by
    rw [← T.p_g, ← Category.assoc, ← hm', Category.assoc, rg.hom_g]
    rfl

include hm hm' in
/-- The refinement of the compactifications of `f` underlying `Triangle.homOfRestrict`. -/
noncomputable def homOfRestrictRf : (ofRestrict d e).cf.Refinement T.cf where
  hom := T.isPullback.lift e.restrict.g (pullback.fst e.g d.i ≫ m) (by
    rw [Category.assoc, ← hm', ← rg.i_hom, restrict_g, ← Category.assoc, ← pullback.condition,
      Category.assoc])
  i_hom := by
    apply T.isPullback.hom_ext
    · change e.restrict.i ≫ T.isPullback.lift _ _ _ ≫ T.cf.g = _
      rw [IsPullback.lift_fst, ← T.cf.comm]
      exact (e.restrict.comm).symm
    · change e.restrict.i ≫ T.isPullback.lift _ _ _ ≫ T.q = _
      rw [IsPullback.lift_snd, restrict_i_fst_assoc, hm, T.i_q]
  hom_g := IsPullback.lift_fst _ _ _ _

include hm hm' in
lemma homOfRestrictRf_hom_q :
    (homOfRestrictRf T d rg e m hm hm').hom ≫ T.q = pullback.fst e.g d.i ≫ m :=
  T.isPullback.lift_snd _ _ _

include hrg hm hm' in
/-- **A morphism of triangles out of a restricted triangle**: for a compactification `d` of `g`
refining `T.cg` with cartesian square, a compactification `e` of `f ≫ d.i` whose open immersion
is scheme-theoretically dominant, and a map `m : e.Z ⟶ T.cfg.Z` compatible with the open
immersions and with `p`, the morphism of triangles `ofRestrict d e ⟶ T`. -/
noncomputable def homOfRestrict [QuasiCompact f] [QuasiCompact e.i]
    [IsSchemeTheoreticallyDominant e.i] :
    (ofRestrict d e).Hom T where
  rf := homOfRestrictRf T d rg e m hm hm'
  rg := rg
  rfg := homOfRestrictRfg T d rg e m hm hm'
  q_comm := homOfRestrictRf_hom_q T d rg e m hm hm'
  p_comm := hm'
  isPullback_rf := by
    have : QuasiCompact e.restrict.i := e.restrict.quasiCompact_openImmersion ‹_›
    have : QuasiCompact (e.restrict.i ≫ pullback.fst e.g d.i) := by
      rw [restrict_i_fst]; infer_instance
    have : IsSchemeTheoreticallyDominant (e.restrict.i ≫ pullback.fst e.g d.i) := by
      rw [restrict_i_fst]; infer_instance
    have : IsSchemeTheoreticallyDominant (ofRestrict d e).cf.i :=
      IsSchemeTheoreticallyDominant.of_comp e.restrict.i (pullback.fst e.g d.i)
    have : QuasiCompact (ofRestrict d e).cf.i := e.restrict.quasiCompact_openImmersion ‹_›
    exact Refinement.isPullback_of_isSchemeTheoreticallyDominant _
  isPullback_rg := hrg

end HomOfRestrict


section Inf

variable [QuasiCompact g] (T₁ T₂ : Triangle f g)

/-- The immersion of `X` into `W = (T₁.cfg.Z ×_{T₁.cg.Z} d.Z) ×_{d.Z} (T₂.cfg.Z ×_{T₂.cg.Z} d.Z)`,
for `d` the common refinement of `T₁.cg` and `T₂.cg`, whose closure is the common refinement of
the triangles `T₁` and `T₂`. -/
noncomputable def infLift : X ⟶ pullback (pullback.snd T₁.p (infFst T₁.cg T₂.cg).hom)
    (pullback.snd T₂.p (infSnd T₁.cg T₂.cg).hom) :=
  pullback.lift
    (pullback.lift T₁.cfg.i (f ≫ (inf T₁.cg T₂.cg).i)
      (by rw [cfg_i_p, Category.assoc, (infFst _ _).i_hom]))
    (pullback.lift T₂.cfg.i (f ≫ (inf T₁.cg T₂.cg).i)
      (by rw [cfg_i_p, Category.assoc, (infSnd _ _).i_hom]))
    (by simp)

@[reassoc (attr := simp)]
lemma infLift_fst_fst : T₁.infLift T₂ ≫ pullback.fst _ _ ≫ pullback.fst _ _ = T₁.cfg.i := by
  simp [infLift]

@[reassoc (attr := simp)]
lemma infLift_snd_fst : T₁.infLift T₂ ≫ pullback.snd _ _ ≫ pullback.fst _ _ = T₂.cfg.i := by
  simp [infLift]

@[reassoc (attr := simp)]
lemma infLift_fst_snd :
    T₁.infLift T₂ ≫ pullback.fst _ _ ≫ pullback.snd _ _ = f ≫ (inf T₁.cg T₂.cg).i := by
  simp [infLift]

instance : IsImmersion (T₁.infLift T₂) :=
  have : IsImmersion (T₁.infLift T₂ ≫ pullback.fst _ _ ≫ pullback.fst _ _) := by
    rw [infLift_fst_fst]; infer_instance
  .of_comp _ (pullback.fst _ _ ≫ pullback.fst _ _)

instance [QuasiCompact (f ≫ g)] : QuasiCompact (T₁.infLift T₂) :=
  have : QuasiCompact (T₁.infLift T₂ ≫ pullback.fst _ _ ≫ pullback.fst _ _) := by
    rw [infLift_fst_fst]; exact T₁.cfg.quasiCompact_openImmersion inferInstance
  .of_comp _ (pullback.fst _ _ ≫ pullback.fst _ _)

/-- The compactification of `f ≫ d.i`, for `d` the common refinement of `T₁.cg` and `T₂.cg`:
the closure of `X` in `(T₁.cfg.Z ×_{T₁.cg.Z} d.Z) ×_{d.Z} (T₂.cfg.Z ×_{T₂.cg.Z} d.Z)`. -/
noncomputable def infCompactification [QuasiCompact (f ≫ g)] :
    Compactification (f ≫ (inf T₁.cg T₂.cg).i) :=
  (Compactification.ofIsImmersion (T₁.infLift T₂)
    (pullback.fst _ _ ≫ pullback.snd T₁.p (infFst T₁.cg T₂.cg).hom)).copy
    (by rw [infLift_fst_snd])

instance [QuasiCompact (f ≫ g)] : QuasiCompact (T₁.infCompactification T₂).i :=
  inferInstanceAs (QuasiCompact (T₁.infLift T₂).toImage)

instance [QuasiCompact (f ≫ g)] : IsSchemeTheoreticallyDominant (T₁.infCompactification T₂).i :=
  inferInstanceAs (IsSchemeTheoreticallyDominant (T₁.infLift T₂).toImage)

/-- **The common refinement of two triangles of compactifications.** -/
noncomputable def inf [QuasiCompact (f ≫ g)] : Triangle f g :=
  ofRestrict (Compactification.inf T₁.cg T₂.cg) (T₁.infCompactification T₂)

/-- The common refinement of two triangles refines the first one. -/
noncomputable def infFst [QuasiCompact (f ≫ g)] : (T₁.inf T₂).Hom T₁ :=
  have : IsSeparated g := T₁.cg.isSeparated
  have : QuasiCompact f := .of_comp f g
  homOfRestrict T₁ _ (Compactification.infFst T₁.cg T₂.cg)
    (Compactification.isPullback_infFst T₁.cg T₂.cg) _
    ((T₁.infLift T₂).imageι ≫ pullback.fst _ _ ≫ pullback.fst _ _)
    (by
      change (T₁.infLift T₂).toImage ≫ _ = _
      rw [Scheme.Hom.toImage_imageι_assoc, infLift_fst_fst])
    (by
      change ((T₁.infLift T₂).imageι ≫ pullback.fst _ _ ≫ pullback.snd _ _) ≫ _ = _
      simp only [Category.assoc, ← pullback.condition])

/-- The common refinement of two triangles refines the second one. -/
noncomputable def infSnd [QuasiCompact (f ≫ g)] : (T₁.inf T₂).Hom T₂ :=
  have : IsSeparated g := T₁.cg.isSeparated
  have : QuasiCompact f := .of_comp f g
  homOfRestrict T₂ _ (Compactification.infSnd T₁.cg T₂.cg)
    (Compactification.isPullback_infSnd T₁.cg T₂.cg) _
    ((T₁.infLift T₂).imageι ≫ pullback.snd _ _ ≫ pullback.fst _ _)
    (by
      change (T₁.infLift T₂).toImage ≫ _ = _
      rw [Scheme.Hom.toImage_imageι_assoc, infLift_snd_fst])
    (by
      change ((T₁.infLift T₂).imageι ≫ pullback.fst _ _ ≫ pullback.snd _ _) ≫ _ = _
      simp only [Category.assoc, pullback.condition])

end Inf


section Canonical

variable (f g) in
/-- The triangle of compactifications attached to the chosen compactifications of `g` and of
`f ≫ g` (`AlgebraicGeometry.HasCompactification.compactification`): `ofRestrict d e` for the
chosen compactification `d` of `g` and `e = Compactification.ofComp` of `f ≫ d.i`. -/
noncomputable def ofHasCompactification [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact (f ≫ g)] : Triangle f g :=
  ofRestrict (HasCompactification.compactification g)
    ((HasCompactification.compactification (f ≫ g)).ofComp _)

/-- The triangle `(𝟙 X, f)`: the trivial compactification of `𝟙 X`, a compactification `c` of `f`
and `c` itself as a compactification of `𝟙 X ≫ f`, with `q = c.i` and `p = 𝟙`. -/
@[simps]
def unitLeft (c : Compactification f) : Triangle (𝟙 X) f where
  cf := ofIsProper (𝟙 X)
  cg := c
  cfg := c.copy (Category.id_comp f)
  q := c.i
  p := 𝟙 c.Z
  i_q := Category.id_comp _
  p_g := Category.id_comp _
  isPullback := by
    change IsPullback (𝟙 X) c.i c.i (𝟙 c.Z)
    exact IsPullback.of_horiz_isIso ⟨by simp⟩

/-- The triangle `(f, 𝟙 Y)`: a compactification `c` of `f`, the trivial compactification of
`𝟙 Y` and `c` itself as a compactification of `f ≫ 𝟙 Y`, with `q = 𝟙` and `p = c.g`. -/
@[simps]
def unitRight (c : Compactification f) : Triangle f (𝟙 Y) where
  cf := c
  cg := ofIsProper (𝟙 Y)
  cfg := c.copy (Category.comp_id f)
  q := 𝟙 c.Z
  p := c.g
  i_q := Category.comp_id _
  p_g := Category.comp_id _
  isPullback := by
    change IsPullback c.g (𝟙 c.Z) (𝟙 Y) c.g
    exact IsPullback.of_vert_isIso ⟨by simp⟩

end Canonical

end Triangle

end AlgebraicGeometry.Compactification
