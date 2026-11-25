/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Fully faithfulness of `MorphismProperty.Over.map`, and the coherence of base change

The functor `MorphismProperty.Over.map` given by post-composition with a morphism
satisfying `P` is always faithful (`CategoryTheory.MorphismProperty.Over.faithful_map`),
and it is full when the morphism is a monomorphism
(`CategoryTheory.MorphismProperty.Over.full_map`).

Base change along a morphism `f : X ⟶ Y` sends a morphism of `P.Over Q Y` to a cartesian
square (`CategoryTheory.MorphismProperty.Over.isPullback_map_left`).

Mathlib provides the composition isomorphism `MorphismProperty.Over.pullbackComp` for base
change, but neither the identity isomorphism nor any coherence law. Both are added here, so
that `X ↦ P.Over Q X` becomes a pseudofunctor in all but name.

## Main declarations

- `CategoryTheory.MorphismProperty.Over.pullbackId`: base change along `𝟙 X` is the identity
  functor of `P.Over Q X`.
- `CategoryTheory.MorphismProperty.Over.pullbackComp_id_left` and
  `CategoryTheory.MorphismProperty.Over.pullbackComp_id_right`: the two unit laws, expressing
  `MorphismProperty.Over.pullbackComp` for `𝟙 X ≫ g` resp. `f ≫ 𝟙 Z` through
  `MorphismProperty.Over.pullbackId`, `MorphismProperty.Over.pullbackCongr` and the unitors.
- `CategoryTheory.MorphismProperty.Over.pullbackCongr_refl`: comparing base change along `f`
  with itself gives the identity isomorphism.
- `CategoryTheory.MorphismProperty.Over.pullbackComp_assoc`: the associativity law, stating
  that the two ways of building `Over.pullback (f ≫ g ≫ h) ≅ Over.pullback h ⋙
  Over.pullback g ⋙ Over.pullback f` out of `MorphismProperty.Over.pullbackComp` agree.

## Implementation notes

`MorphismProperty.Over.pullbackComp f g` takes the composite `f ≫ g` as an optional argument
`fg` together with a proof `hfg : fg = f ≫ g`, so that base change along a morphism that is
only propositionally a composite is covered. The three coherence laws below keep that shape:
each takes the composite it is about as an optional argument, defaulting to the reduced
morphism (`g`, `f` and `f ≫ g ≫ h` respectively). Thus `Over.pullbackComp_id_left g` is the
unit law in its reduced form `Over.pullback P Q g ≅ Over.pullback P Q g ⋙ 𝟭`, while
`Over.pullbackComp_id_left g (𝟙 X ≫ g) rfl` is the law for `Over.pullbackComp (𝟙 X) g` with
its own default composite, which is the form produced by consumers such as
`CategoryTheory.GrothendieckTopology.lowerStarComp`.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace CategoryTheory

variable {T : Type*} [Category T] {P Q : MorphismProperty T} [Q.IsMultiplicative]
  {X Y : T}

section Map

variable [P.IsStableUnderComposition] {f : X ⟶ Y} (hPf : P f)

/-- The functor `MorphismProperty.Over.map` given by post-composition with `f` is always
faithful: it acts as the identity on the underlying morphisms. -/
instance MorphismProperty.Over.faithful_map : (MorphismProperty.Over.map Q hPf).Faithful where
  map_injective {A B} {φ ψ} h := by
    apply MorphismProperty.Over.Hom.ext
    have h' : ((MorphismProperty.Over.map Q hPf).map φ).left =
        ((MorphismProperty.Over.map Q hPf).map ψ).left := by rw [h]
    simpa using h'

/-- For a monomorphism `f`, the functor `MorphismProperty.Over.map` given by
post-composition with `f` is full: the compatibility with the structure morphisms over
the target can be cancelled along `f`. -/
instance MorphismProperty.Over.full_map [Mono f] : (MorphismProperty.Over.map Q hPf).Full where
  map_surjective {A B} ψ := by
    refine ⟨MorphismProperty.Over.homMk ψ.left ?_ ψ.prop_hom_left, ?_⟩
    · rw [← cancel_mono f]
      simpa using MorphismProperty.Over.w ψ
    · apply MorphismProperty.Over.Hom.ext
      simp

end Map

section Pullback

variable [Q.IsStableUnderBaseChange] (f : X ⟶ Y) [P.HasPullbacksAlong f]
  [P.IsStableUnderBaseChangeAlong f]

/-- Base change along `f : X ⟶ Y` sends a morphism `φ : A ⟶ B` of `P.Over Q Y` to a
cartesian square: it exhibits `A ×_Y X` as the fibre product of `A` and `B ×_Y X` over `B`.

```
  A ×_Y X ──(Over.pullback P Q f).map φ──→ B ×_Y X
     │                                        │
     │ pullback.fst A.hom f                   │ pullback.fst B.hom f
     ↓                                        ↓
     A ──────────────── φ.left ─────────────→ B
```
-/
lemma MorphismProperty.Over.isPullback_map_left {A B : P.Over Q Y} (φ : A ⟶ B) :
    IsPullback (pullback.fst A.hom f) ((MorphismProperty.Over.pullback P Q f).map φ).left φ.left
      (pullback.fst B.hom f) := by
  refine IsPullback.of_bot ?_ (by simp) (IsPullback.of_hasPullback B.hom f)
  have h : ((MorphismProperty.Over.pullback P Q f).map φ).left ≫ pullback.snd B.hom f =
      pullback.snd A.hom f := by
    simp
  rw [h, MorphismProperty.Over.w φ]
  exact IsPullback.of_hasPullback A.hom f

end Pullback

section PullbackCoherence

namespace MorphismProperty

variable (P Q) [Q.RespectsIso] [Q.IsStableUnderBaseChange]

/-- Base change along `𝟙 X` is the identity functor of `P.Over Q X`: the isomorphism is given
by the first projection `A ×_X X ≅ A`. -/
@[simps! hom_app_left inv_app_left]
noncomputable def Over.pullbackId (X : T) [P.HasPullbacksAlong (𝟙 X)]
    [P.IsStableUnderBaseChangeAlong (𝟙 X)] :
    Over.pullback P Q (𝟙 X) ≅ 𝟭 (P.Over Q X) :=
  NatIso.ofComponents (fun A ↦ Over.isoMk
    { hom := pullback.fst A.hom (𝟙 X)
      inv := pullback.lift (𝟙 A.left) A.hom (by simp)
      hom_inv_id := by apply pullback.hom_ext <;> simp [pullback.condition]
      inv_hom_id := by simp }
    (by simpa using pullback.condition (f := A.hom) (g := 𝟙 X)))
    (by intros; apply Over.Hom.ext; simp)

variable {P Q}

@[reassoc (attr := simp)]
lemma Over.pullbackId_inv_app_left_fst {X : T} [P.HasPullbacksAlong (𝟙 X)]
    [P.IsStableUnderBaseChangeAlong (𝟙 X)] (A : P.Over Q X) :
    ((Over.pullbackId P Q X).inv.app A).left ≫ pullback.fst A.hom (𝟙 X) = 𝟙 A.left := by
  simp

omit [Q.RespectsIso] in
/-- Base change along `f` compared with itself through a proof of `f = f` is the identity
isomorphism. -/
@[simp]
lemma Over.pullbackCongr_refl (f : X ⟶ Y) [P.HasPullbacksAlong f]
    [P.IsStableUnderBaseChangeAlong f] (h : f = f) :
    Over.pullbackCongr (P := P) (Q := Q) h = Iso.refl (Over.pullback P Q f) := by
  ext A : 4
  apply pullback.hom_ext <;> simp [Over.pullbackCongr, Over.pullback, Over.mk]

section Unit

variable {X Z : T}

/-- The left unit law for `MorphismProperty.Over.pullbackComp`: base change along a morphism
of the form `𝟙 X ≫ g` is base change along `g`, followed by the identity functor. -/
lemma Over.pullbackComp_id_left (g : X ⟶ Z) [P.IsStableUnderBaseChangeAlong g]
    [P.HasPullbacksAlong g] [P.IsStableUnderBaseChangeAlong (𝟙 X)] [P.HasPullbacksAlong (𝟙 X)]
    (fg : X ⟶ Z := g) (hfg : fg = 𝟙 X ≫ g := by cat_disch) :
    haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
    haveI : P.IsStableUnderBaseChangeAlong fg := by subst hfg; infer_instance
    Over.pullbackComp (𝟙 X) g fg hfg =
      Over.pullbackCongr (hfg.trans (id_comp g)) ≪≫ (Over.pullback P Q g).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (Over.pullback P Q g) (Over.pullbackId P Q X).symm := by
  subst hfg
  ext A : 4
  apply pullback.hom_ext (f := pullback.snd A.hom g) (g := 𝟙 X)
  · apply pullback.hom_ext <;>
      simp [Over.pullback, Over.mk, Over.pullbackCongr, pullback.condition]
  · simp [Over.pullback, Over.mk, Over.pullbackCongr]

/-- The right unit law for `MorphismProperty.Over.pullbackComp`: base change along a morphism
of the form `f ≫ 𝟙 Z` is the identity functor, followed by base change along `f`. -/
lemma Over.pullbackComp_id_right (f : X ⟶ Z) [P.IsStableUnderBaseChangeAlong f]
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong (𝟙 Z)] [P.HasPullbacksAlong (𝟙 Z)]
    (fg : X ⟶ Z := f) (hfg : fg = f ≫ 𝟙 Z := by cat_disch) :
    haveI : P.HasPullbacksAlong fg := by subst hfg; infer_instance
    haveI : P.IsStableUnderBaseChangeAlong fg := by subst hfg; infer_instance
    Over.pullbackComp f (𝟙 Z) fg hfg =
      Over.pullbackCongr (hfg.trans (comp_id f)) ≪≫ (Over.pullback P Q f).leftUnitor.symm ≪≫
        Functor.isoWhiskerRight (Over.pullbackId P Q Z).symm (Over.pullback P Q f) := by
  subst hfg
  ext A : 4
  apply pullback.hom_ext (f := pullback.snd A.hom (𝟙 Z)) (g := f)
  · apply pullback.hom_ext
    · simp [Over.pullback, Over.mk, Over.pullbackCongr]
    · have h : pullback.snd A.hom (f ≫ 𝟙 Z) ≫ f = pullback.fst A.hom (f ≫ 𝟙 Z) ≫ A.hom := by
        simpa using (pullback.condition (f := A.hom) (g := f ≫ 𝟙 Z)).symm
      simp [Over.pullback, Over.mk, Over.pullbackCongr, h]
  · simp [Over.pullback, Over.mk, Over.pullbackCongr]

end Unit

section Assoc

variable {X Y Z W : T}

/-- The associativity law for `MorphismProperty.Over.pullbackComp`: the two ways of writing
base change along `f ≫ g ≫ h` as base change along `h`, then along `g`, then along `f`
agree. -/
lemma Over.pullbackComp_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [P.IsStableUnderBaseChangeAlong f] [P.IsStableUnderBaseChangeAlong g]
    [P.IsStableUnderBaseChangeAlong h] [P.HasPullbacksAlong f] [P.HasPullbacksAlong g]
    [P.HasPullbacksAlong h] (fgh : X ⟶ W := f ≫ g ≫ h)
    (hfgh : fgh = f ≫ g ≫ h := by cat_disch) :
    haveI : P.HasPullbacksAlong fgh := by subst hfgh; infer_instance
    haveI : P.IsStableUnderBaseChangeAlong fgh := by subst hfgh; infer_instance
    Over.pullbackComp f (g ≫ h) fgh hfgh ≪≫
        Functor.isoWhiskerRight (Over.pullbackComp g h) (Over.pullback P Q f) ≪≫
          Functor.associator _ _ _ =
      Over.pullbackComp (f ≫ g) h fgh (by rw [hfgh, assoc]) ≪≫
        Functor.isoWhiskerLeft (Over.pullback P Q h) (Over.pullbackComp f g) := by
  subst hfgh
  ext A : 4
  have : HasPullback (pullback.snd (pullback.snd A.hom h) g) f :=
    HasPullbacksAlong.hasPullback _ (P.pullback_snd _ _ (P.pullback_snd A.hom h A.prop))
  apply pullback.hom_ext (f := pullback.snd (pullback.snd A.hom h) g) (g := f)
  · apply pullback.hom_ext (f := pullback.snd A.hom h) (g := g)
    · apply pullback.hom_ext <;> simp [Over.pullback, Over.mk]
    · simp [Over.pullback, Over.mk]
  · simp [Over.pullback, Over.mk]

end Assoc

end MorphismProperty

end PullbackCoherence

section PullbackMapComparison

variable [P.IsStableUnderComposition] {U' U Z' Z : T} {g' : U' ⟶ U} {j' : U' ⟶ Z'}
  {j : U ⟶ Z} {g'' : Z' ⟶ Z} (hj : P j) (hj' : P j') [P.HasPullbacksAlong g']
  [P.IsStableUnderBaseChangeAlong g'] [P.HasPullbacksAlong g'']
  [P.IsStableUnderBaseChangeAlong g'']

/-- The **Beck–Chevalley comparison** attached to a commutative square `g' ≫ j = j' ≫ g''`
with `j` and `j'` in `P`

```
U' --j'--> Z'
|          |
g'         g''
v          v
U  --j-->  Z
```

is the natural transformation
`Over.pullback g' ⋙ Over.map j' ⟶ Over.map j ⋙ Over.pullback g''` of functors
`P.Over ⊤ U ⥤ P.Over ⊤ Z'`

```
P.Over ⊤ U --Over.pullback g'--> P.Over ⊤ U'
    |                                |
 Over.map j          ⇙          Over.map j'
    v                                v
P.Over ⊤ Z --Over.pullback g''--> P.Over ⊤ Z'
```

sending `T ⟶ U` to the canonical morphism `T ×_U U' ⟶ T ×_Z Z'` over `Z'`. -/
@[simps! app_left]
noncomputable def MorphismProperty.Over.pullbackMapComparison (sq : CommSq g' j' j g'') :
    Over.pullback P ⊤ g' ⋙ Over.map ⊤ hj' ⟶ Over.map ⊤ hj ⋙ Over.pullback P ⊤ g'' where
  app b := Over.homMk
    (pullback.lift (f := ((Over.map ⊤ hj).obj b).hom) (g := g'') (pullback.fst b.hom g')
      (pullback.snd b.hom g' ≫ j') (by simp [pullback.condition_assoc, sq.w]))
    (by simp) trivial
  naturality b b' f := by
    ext
    apply pullback.hom_ext <;> simp

/-- For a cartesian square, the Beck–Chevalley comparison
`Over.pullback g' ⋙ Over.map j' ⟶ Over.map j ⋙ Over.pullback g''` is an isomorphism:
pasting the cartesian square of `T ×_U U'` with the given one identifies `T ×_U U'` with
`T ×_Z Z'`. -/
lemma MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (hsq : IsPullback g' j' j g'') :
    IsIso (Over.pullbackMapComparison hj hj' hsq.toCommSq) := by
  have (b : P.Over ⊤ U) : IsIso ((Over.pullbackMapComparison hj hj' hsq.toCommSq).app b) := by
    have h : IsPullback (pullback.fst b.hom g') (pullback.snd b.hom g' ≫ j')
        ((Over.map ⊤ hj).obj b).hom g'' :=
      (IsPullback.of_hasPullback b.hom g').paste_vert hsq
    have hleft : ((Over.pullbackMapComparison hj hj' hsq.toCommSq).app b).left =
        h.isoPullback.hom := by
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans (IsPullback.isoPullback_hom_fst h).symm
      · exact (pullback.lift_snd _ _ _).trans (IsPullback.isoPullback_hom_snd h).symm
    rw [← isIso_iff_of_reflects_iso _ (Over.forget P ⊤ Z' ⋙ CategoryTheory.Over.forget Z'),
      Over.forget_comp_forget_map, hleft]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end PullbackMapComparison

section PullbackCongr

set_option backward.defeqAttrib.useBackward true in
/-- The base change isomorphism along an equality `f = g` is compatible with the second
projections. This complements mathlib's
`CategoryTheory.MorphismProperty.Over.pullbackCongr_hom_app_left_fst`. -/
@[reassoc (attr := simp)]
lemma MorphismProperty.Over.pullbackCongr_hom_app_left_snd {f g : X ⟶ Y}
    [P.HasPullbacksAlong f] [P.IsStableUnderBaseChangeAlong f] [Q.IsStableUnderBaseChange]
    (h : f = g) (B : P.Over Q Y) :
    haveI : P.HasPullbacksAlong g := by subst h; infer_instance
    ((MorphismProperty.Over.pullbackCongr h).hom.app B).left ≫ pullback.snd B.hom g =
      pullback.snd B.hom f := by
  subst h
  simp [MorphismProperty.Over.pullbackCongr]

end PullbackCongr


end CategoryTheory

namespace CategoryTheory.MorphismProperty.Over

section Slice

variable {C : Type*} [Category C] {P : MorphismProperty C} [P.IsStableUnderComposition]
  [P.HasOfPostcompProperty P] {X Y : C} {f : X ⟶ Y} (hPf : P f) (T : P.Over ⊤ X)

/-- Composition with `f` induces a full functor on the slices over each object: a morphism
over `X` between two objects over `T` which is compatible with the maps to `T ⟶ Y` is a morphism
over `X`. -/
instance full_post_map_op : (Under.post (Over.map ⊤ hPf).op (X := Opposite.op T)).Full where
  map_surjective {A B} ψ := by
    let m := ψ.right.unop
    have hA := Over.w A.hom.unop
    have hB := Over.w B.hom.unop
    have hψ' : m ≫ (Over.map ⊤ hPf).map A.hom.unop = (Over.map ⊤ hPf).map B.hom.unop :=
      Quiver.Hom.op_inj (CategoryTheory.Under.w ψ)
    have hψ : m.left ≫ A.hom.unop.left = B.hom.unop.left := by
      simpa using congrArg (fun φ ↦ φ.left) hψ'
    let φ : B.right.unop ⟶ A.right.unop := Over.homMk m.left (by
      rw [← hA, ← Category.assoc, hψ, hB]) trivial
    refine ⟨CategoryTheory.Under.homMk φ.op ?_, ?_⟩
    · apply Quiver.Hom.unop_inj
      apply Over.Hom.ext
      simpa [φ] using hψ
    · ext
      rfl

/-- Composition with `f` is essentially surjective on the slices over each object `T`: an
object `s : W ⟶ T` over `T` is an object over `X` through `T`, using that `P` has the
right-cancellation property. -/
instance essSurj_post_map_op :
    (Under.post (Over.map ⊤ hPf).op (X := Opposite.op T)).EssSurj where
  mem_essImage Z := by
    let s := Z.hom.unop
    have hs : P s.left := MorphismProperty.of_postcomp (W := P) (W' := P) s.left (T.hom ≫ f)
      (P.comp_mem _ _ T.prop hPf) (by
        have : s.left ≫ T.hom ≫ f = Z.right.unop.hom := Over.w s
        rw [this]
        exact Z.right.unop.prop)
    let W : P.Over ⊤ X := Over.mk ⊤ (s.left ≫ T.hom) (P.comp_mem _ _ hs T.prop)
    let t : W ⟶ T := Over.homMk s.left rfl trivial
    refine ⟨CategoryTheory.Under.mk t.op, ⟨CategoryTheory.Under.isoMk
      (Iso.op (Over.isoMk (Iso.refl _) ?_)) ?_⟩⟩
    · have : s.left ≫ T.hom ≫ f = Z.right.unop.hom := Over.w s
      simpa [W] using this
    · apply Quiver.Hom.unop_inj
      apply Over.Hom.ext
      simp [W, t, s]

/-- Composition with `f` induces equivalences on the slices over each object. -/
instance isEquivalence_post_map_op :
    (Under.post (Over.map ⊤ hPf).op (X := Opposite.op T)).IsEquivalence where

end Slice

end CategoryTheory.MorphismProperty.Over
