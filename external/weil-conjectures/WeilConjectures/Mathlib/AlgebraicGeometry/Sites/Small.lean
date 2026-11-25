/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.CommaSites
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!

# Continuity of base change and of localization for the small sites

Base change along an arbitrary morphism is continuous for the small `Q`-topologies of
`P`-schemes, for `Q ≤ P`: it preserves covers because covers are jointly surjective
families of `Q`-morphisms and the base change square is cartesian, and it preserves
compatible families because it is representably flat, the small site being finitely
complete.

The localization functor `MorphismProperty.Over.map ⊤ h` along `h : P f`, that is,
composition with `f`, is continuous *and* cocontinuous for the same topologies, again for
`Q ≤ P`: covering sieves are transported in both directions essentially by reindexing, and
compatible families are preserved because the cancellation property
`P.HasOfPostcompProperty P` turns a morphism between `P`-schemes over `U` into a morphism
of `P`-schemes over `V`.

## Main results

- `AlgebraicGeometry.Scheme.coverPreserving_overPullback`: base change along an arbitrary
  morphism preserves the covering sieves of the small `Q`-topologies.
- `AlgebraicGeometry.Scheme.isContinuous_overPullback`: base change along an arbitrary
  morphism is continuous for the small `Q`-topologies.
- `AlgebraicGeometry.Scheme.coverPreserving_overMap`,
  `AlgebraicGeometry.Scheme.compatiblePreserving_overMap`,
  `AlgebraicGeometry.Scheme.isContinuous_overMap` and
  `AlgebraicGeometry.Scheme.isCocontinuous_overMap`: the localization functor is continuous
  and cocontinuous for the small `Q`-topologies, with instances for `Q = P`.
- `AlgebraicGeometry.Scheme.isContinuous_overForget`: the forgetful functor from the small
  `Q`-site of `P`-schemes to `S`-schemes is continuous.
- `AlgebraicGeometry.Scheme.isContinuous_overMap_comp_overPullback` and
  `AlgebraicGeometry.Scheme.isContinuous_overPullback_comp_overMap`: the two composites of
  base change and localization are continuous for the small `P`-topologies.

-/

@[expose] public section

set_option linter.style.show false

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (P Q : MorphismProperty Scheme.{u})
  [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]

/-! ### Base change -/

/-- Base change along an *arbitrary* morphism `g : W ⟶ U` preserves the covering sieves of
the small `Q`-topologies of `P`-schemes, for `Q ≤ P`.

Both squares below are cartesian, so a point `x` of `V ×_U W` and a preimage `w` of its
image in `V` under a covering morphism `φ.left` are jointly a point of `V' ×_U W`:

```
  V' ×_U W ──(Over.pullback P ⊤ g).map φ──→ V ×_U W ──────→ W
      │                                        │            │
      │ pullback.fst V'.hom g                  │ fst V.hom g│ g
      ↓                                        ↓            ↓
      V' ───────────── φ.left ──────────────→ V ──V.hom──→ U
```
-/
lemma coverPreserving_overPullback (hQP : Q ≤ P) {W U : Scheme.{u}} (g : W ⟶ U) :
    CoverPreserving (U.smallGrothendieckTopology Q (Q := P))
      (W.smallGrothendieckTopology Q (Q := P)) (MorphismProperty.Over.pullback P ⊤ g) where
  cover_preserve {V S} hS := by
    rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology U hQP] at hS
    rw [smallGrothendieckTopology_eq_toGrothendieck_smallPretopology W hQP]
    replace hS := (mem_toGrothendieck_smallPretopology _ _).mp hS
    refine (mem_toGrothendieck_smallPretopology _ _).mpr fun x ↦ ?_
    obtain ⟨V', φ, w, hSφ, hφl, hφw⟩ := hS (pullback.fst V.hom g x)
    have h := MorphismProperty.Over.isPullback_map_left g φ
    obtain ⟨ξ, -, hξ⟩ := Scheme.exists_preimage_of_isPullback h w x hφw
    exact ⟨_, (MorphismProperty.Over.pullback P ⊤ g).map φ, ξ,
      ⟨V', φ, 𝟙 _, hSφ, (Category.id_comp _).symm⟩, Q.of_isPullback h hφl, hξ⟩

/-- Base change along an *arbitrary* morphism `g : W ⟶ U` is continuous for the small
`Q`-topologies of `P`-schemes, for `Q ≤ P`. -/
theorem isContinuous_overPullback (hQP : Q ≤ P) {W U : Scheme.{u}} (g : W ⟶ U) :
    (MorphismProperty.Over.pullback P ⊤ g).IsContinuous
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P)) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ _) (coverPreserving_overPullback P Q hQP g)

/-! ### The forgetful functor -/

/-- The forgetful functor from `P`-schemes over `S` to `S`-schemes is continuous for the small
`Q`-topology and the `Q`-topology on `Over S`, for `Q ≤ P`: it preserves covers by definition
of the small topology, and compatible families since it is representably flat. -/
lemma isContinuous_overForget (hQP : Q ≤ P) (S : Scheme.{u}) :
    (MorphismProperty.Over.forget P ⊤ S).IsContinuous
      (S.smallGrothendieckTopology Q (Q := P)) (S.overGrothendieckTopology Q) :=
  have := locallyCoverDense_of_le S hQP
  have : RepresentablyFlat (MorphismProperty.Over.forget P ⊤ S) :=
    flat_of_preservesFiniteLimits _
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (Functor.coverPreserving_restrictedTopology _ _)

instance (S : Scheme.{u}) :
    (MorphismProperty.Over.forget P ⊤ S).IsContinuous
      (S.smallGrothendieckTopology P) (S.overGrothendieckTopology P) :=
  isContinuous_overForget P P le_rfl S

/-! ### The localization functor -/

section OverMap

variable {P Q} {V U : Scheme.{u}} {f : V ⟶ U} (h : P f)

/-- For `Q ≤ P` the localization functor is cocontinuous for the small `Q`-topologies. -/
lemma isCocontinuous_overMap (hQP : Q ≤ P) :
    (MorphismProperty.Over.map ⊤ h).IsCocontinuous
      (V.smallGrothendieckTopology Q (Q := P)) (U.smallGrothendieckTopology Q (Q := P)) where
  cover_lift {W S} hS := by
    have heqV : V.smallGrothendieckTopology Q (Q := P) =
        (V.smallPretopology Q P).toGrothendieck :=
      smallGrothendieckTopology_eq_toGrothendieck_smallPretopology V hQP
    have heqU : U.smallGrothendieckTopology Q (Q := P) =
        (U.smallPretopology Q P).toGrothendieck :=
      smallGrothendieckTopology_eq_toGrothendieck_smallPretopology U hQP
    rw [heqU] at hS
    rw [heqV]
    replace hS := (mem_toGrothendieck_smallPretopology _ _).mp hS
    refine (mem_toGrothendieck_smallPretopology _ _).mpr fun x => ?_
    obtain ⟨Y, φ, y, hSφ, hφl, hφy⟩ := hS x
    let W' : P.Over ⊤ V := MorphismProperty.Over.mk ⊤ (φ.left ≫ W.hom)
      (P.comp_mem _ _ (hQP _ hφl) W.prop)
    let ψ : W' ⟶ W := MorphismProperty.Over.homMk φ.left rfl
    refine ⟨W', ψ, y, ?_, hφl, hφy⟩
    -- Compare the image of `ψ` under the localization functor with `φ` via the identity
    -- on `Y.left`.
    have hY : 𝟙 Y.left ≫ Y.hom = (φ.left ≫ W.hom) ≫ f := by
      simp only [Category.id_comp, Category.assoc]
      exact (MorphismProperty.Over.w φ).symm
    let e : (MorphismProperty.Over.map ⊤ h).obj W' ⟶ Y :=
      MorphismProperty.Over.homMk (𝟙 Y.left) hY
    have hge : (MorphismProperty.Over.map ⊤ h).map ψ = e ≫ φ := by
      apply MorphismProperty.Over.Hom.ext
      show φ.left = 𝟙 Y.left ≫ φ.left
      exact (Category.id_comp _).symm
    show S.arrows ((MorphismProperty.Over.map ⊤ h).map ψ)
    rw [hge]
    exact S.downward_closed hSφ e

/-- For `Q ≤ P` the localization functor preserves covering sieves of the small
`Q`-topologies. -/
lemma coverPreserving_overMap (hQP : Q ≤ P) :
    CoverPreserving (V.smallGrothendieckTopology Q (Q := P))
      (U.smallGrothendieckTopology Q (Q := P)) (MorphismProperty.Over.map ⊤ h) where
  cover_preserve {W S} hS := by
    have heqV : V.smallGrothendieckTopology Q (Q := P) =
        (V.smallPretopology Q P).toGrothendieck :=
      smallGrothendieckTopology_eq_toGrothendieck_smallPretopology V hQP
    have heqU : U.smallGrothendieckTopology Q (Q := P) =
        (U.smallPretopology Q P).toGrothendieck :=
      smallGrothendieckTopology_eq_toGrothendieck_smallPretopology U hQP
    rw [heqV] at hS
    rw [heqU]
    replace hS := (mem_toGrothendieck_smallPretopology _ _).mp hS
    refine (mem_toGrothendieck_smallPretopology _ _).mpr fun v => ?_
    obtain ⟨Z, g, z, hSg, hgl, hgz⟩ := hS v
    exact ⟨(MorphismProperty.Over.map ⊤ h).obj Z, (MorphismProperty.Over.map ⊤ h).map g, z,
      ⟨Z, g, 𝟙 _, hSg, (Category.id_comp _).symm⟩, hgl, hgz⟩

omit [Q.IsMultiplicative] [Q.IsStableUnderBaseChange] [P.IsStableUnderBaseChange] in
/-- The localization functor preserves compatible families of elements. This is the case
`K = U.smallGrothendieckTopology Q` of
`CategoryTheory.MorphismProperty.Over.compatiblePreserving_map`, which holds for an
arbitrary topology on `P.Over ⊤ U`. -/
lemma compatiblePreserving_overMap :
    CompatiblePreserving.{w} (U.smallGrothendieckTopology Q (Q := P))
      (MorphismProperty.Over.map ⊤ h) :=
  MorphismProperty.Over.compatiblePreserving_map h _

/-- For `Q ≤ P` the localization functor is continuous for the small `Q`-topologies. -/
lemma isContinuous_overMap (hQP : Q ≤ P) :
    (MorphismProperty.Over.map ⊤ h).IsContinuous
      (V.smallGrothendieckTopology Q (Q := P)) (U.smallGrothendieckTopology Q (Q := P)) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_overMap h)
    (coverPreserving_overMap h hQP)

end OverMap

instance {P : MorphismProperty Scheme} {V U : Scheme} {f : V ⟶ U} (h : P f)
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative] :
    (MorphismProperty.Over.map ⊤ h).IsCocontinuous
      (V.smallGrothendieckTopology P) (U.smallGrothendieckTopology P) :=
  isCocontinuous_overMap h le_rfl

instance {P : MorphismProperty Scheme} {V U : Scheme} {f : V ⟶ U} (h : P f)
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative] :
    (MorphismProperty.Over.map ⊤ h).IsContinuous
      (V.smallGrothendieckTopology P) (U.smallGrothendieckTopology P) :=
  isContinuous_overMap h le_rfl

/-- The localization functor along `h : P f` followed by base change along `g : W ⟶ U` is
continuous for the small `P`-topologies, as a composite of continuous functors. -/
instance isContinuous_overMap_comp_overPullback {P : MorphismProperty Scheme}
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative]
    {V U W : Scheme} {f : V ⟶ U} (h : P f) (g : W ⟶ U) :
    (MorphismProperty.Over.map ⊤ h ⋙ MorphismProperty.Over.pullback P ⊤ g).IsContinuous
      (V.smallGrothendieckTopology P) (W.smallGrothendieckTopology P) :=
  have := isContinuous_overPullback P P le_rfl g
  Functor.isContinuous_comp _ _ _ (U.smallGrothendieckTopology P) _

/-- Base change along `g : W ⟶ U` followed by the localization functor along `h : P f` is
continuous for the small `P`-topologies, as a composite of continuous functors. -/
instance isContinuous_overPullback_comp_overMap {P : MorphismProperty Scheme}
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] [P.IsMultiplicative]
    {V U W : Scheme} (g : W ⟶ U) {f : W ⟶ V} (h : P f) :
    (MorphismProperty.Over.pullback P ⊤ g ⋙ MorphismProperty.Over.map ⊤ h).IsContinuous
      (U.smallGrothendieckTopology P) (V.smallGrothendieckTopology P) :=
  have := isContinuous_overPullback P P le_rfl g
  Functor.isContinuous_comp _ _ _ (W.smallGrothendieckTopology P) _

end AlgebraicGeometry.Scheme
