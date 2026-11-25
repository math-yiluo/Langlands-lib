/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementOfIsPullback

/-!
# Base change of refinements of compactifications over a base scheme

Let `sq : IsPullback g' f' f g` be a cartesian square in `Over S`. This file constructs

- the base change `r.ofIsPullback sq` of a refinement `r : OverRefinement c c₁` of
  compactifications of `f.left`, a refinement of the base changes `c.ofIsPullback sq.overLeft`
  and `c₁.ofIsPullback sq.overLeft` (`Compactification.OverRefinement.ofIsPullback`);
- for a compactification `c'` of `f'.left` lying over a compactification `c` of `f.left` along
  `h : c'.Z ⟶ c.Z` with cartesian squares, the refinement of the base change
  `c.ofIsPullback sq.overLeft` by `c'`, whose map `c'.Z ⟶ c.Z ×_Y Y'` is an isomorphism
  (`Compactification.OverRefinement.toOfIsPullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {S : Scheme.{u}} {X Y X' Y' : Over S} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X}

namespace OverRefinement

variable {c c₁ : Compactification f.left}

/-- The identity refinement of a compactification. -/
@[simps]
noncomputable def refl (c : Compactification f.left) : OverRefinement c c where
  hom := 𝟙 c.overObj
  hom_overG := Category.id_comp _
  isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩
  isProper := inferInstanceAs (IsProper (𝟙 c.Z))

/-- The square of underlying schemes of a refinement is cartesian. -/
theorem isPullback_left (r : OverRefinement c c₁) :
    IsPullback (𝟙 X.left) c.i c₁.i r.hom.left :=
  r.isPullback.map (Over.forget S)

/-- The refinement of compactifications of `f.left` underlying a refinement in `Over S`. -/
@[simps]
noncomputable def toRefinement (r : OverRefinement c c₁) : c.Refinement c₁ where
  hom := r.hom.left
  i_hom := by simpa using r.isPullback_left.w.symm
  hom_g := congrArg CommaMorphism.left r.hom_overG

/-- **Base change of a refinement along a cartesian square** in `Over S`: the refinement
`r.hom ×_Y Y' : c.Z ×_Y Y' ⟶ c₁.Z ×_Y Y'` of `c₁.ofIsPullback sq.overLeft` by
`c.ofIsPullback sq.overLeft`. -/
noncomputable def ofIsPullback (sq : IsPullback g' f' f g) (r : OverRefinement c c₁) :
    OverRefinement (c.ofIsPullback sq.overLeft) (c₁.ofIsPullback sq.overLeft) :=
  overRefinementOfRefinement (r.toRefinement.ofIsPullback sq.overLeft)
    (Refinement.isPullback_ofIsPullback sq.overLeft r.toRefinement r.isPullback_left.flip).flip

@[simp]
lemma ofIsPullback_hom_left (sq : IsPullback g' f' f g) (r : OverRefinement c c₁) :
    (r.ofIsPullback sq).hom.left = (r.toRefinement.ofIsPullback sq.overLeft).hom :=
  rfl

/-- The base change of a refinement commutes with the projections to the compactifications. -/
@[reassoc]
lemma ofIsPullback_hom_overBaseChangeFst (sq : IsPullback g' f' f g) (r : OverRefinement c c₁) :
    (r.ofIsPullback sq).hom ≫ c₁.overBaseChangeFst sq = c.overBaseChangeFst sq ≫ r.hom :=
  Over.OverMorphism.ext (Refinement.ofIsPullback_hom_fst sq.overLeft r.toRefinement)

/-- For a compactification `c'` of `f'.left` lying over a compactification `c` of `f.left`
along `h : c'.Z ⟶ c.Z` with cartesian squares, the map `c'.Z ⟶ c.Z ×_Y Y'`, as a morphism of
`Over S`. -/
noncomputable def toOfIsPullbackHom (sq : IsPullback g' f' f g) (c : Compactification f.left)
    (c' : Compactification f'.left) (h : c'.overObj ⟶ c.overObj)
    (hp : IsPullback h c'.overG c.overG g) : c'.overObj ⟶ (c.ofIsPullback sq.overLeft).overObj :=
  Over.homMk (pullback.lift h.left c'.g (congrArg CommaMorphism.left hp.w)) (by
    change pullback.lift h.left c'.g _ ≫ pullback.snd c.g g.left ≫ Y'.hom = c'.g ≫ Y'.hom
    rw [pullback.lift_snd_assoc])

@[reassoc (attr := simp)]
lemma toOfIsPullbackHom_overBaseChangeFst (sq : IsPullback g' f' f g)
    (c : Compactification f.left) (c' : Compactification f'.left) (h : c'.overObj ⟶ c.overObj)
    (hp : IsPullback h c'.overG c.overG g) :
    toOfIsPullbackHom sq c c' h hp ≫ c.overBaseChangeFst sq = h :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

/-- The comparison `c' ⟶ c.ofIsPullback` is an isomorphism of schemes when `c'` is cartesian over
`c`. -/
instance isIso_toOfIsPullbackHom_left (sq : IsPullback g' f' f g) (c : Compactification f.left)
    (c' : Compactification f'.left) (h : c'.overObj ⟶ c.overObj)
    (hp : IsPullback h c'.overG c.overG g) : IsIso (toOfIsPullbackHom sq c c' h hp).left := by
  have hp' : IsPullback h.left c'.g c.g g.left := hp.map (Over.forget S)
  have : (toOfIsPullbackHom sq c c' h hp).left = hp'.isoPullback.hom :=
    pullback.hom_ext (by simp [toOfIsPullbackHom]) (by simp [toOfIsPullbackHom])
  rw [this]
  infer_instance

/-- **The refinement of a base change by a compactification lying over it**: for a
compactification `c'` of `f'.left` lying over a compactification `c` of `f.left` along
`h : c'.Z ⟶ c.Z` with cartesian squares, the isomorphism `c'.Z ≅ c.Z ×_Y Y'` is a refinement of
`c.ofIsPullback sq.overLeft` by `c'`. -/
noncomputable def toOfIsPullback (sq : IsPullback g' f' f g) (c : Compactification f.left)
    (c' : Compactification f'.left) (h : c'.overObj ⟶ c.overObj)
    (hi : IsPullback g' c'.overI c.overI h) (hp : IsPullback h c'.overG c.overG g) :
    OverRefinement c' (c.ofIsPullback sq.overLeft) where
  hom := toOfIsPullbackHom sq c c' h hp
  hom_overG := Over.OverMorphism.ext (pullback.lift_snd _ _ _)
  isPullback := by
    have := isIso_toOfIsPullbackHom_left sq c c' h hp
    have : IsIso (toOfIsPullbackHom sq c c' h hp) :=
      have : IsIso ((Over.forget S).map (toOfIsPullbackHom sq c c' h hp)) := by
        dsimp; infer_instance
      isIso_of_reflects_iso _ (Over.forget S)
    refine IsPullback.of_horiz_isIso ⟨Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)⟩
    · have := congrArg CommaMorphism.left hi.w
      simp only [Over.comp_left, overI_left] at this
      simpa [toOfIsPullbackHom, overI] using this
    · simp [toOfIsPullbackHom, overI, c'.comm]
  isProper := by
    have := isIso_toOfIsPullbackHom_left sq c c' h hp
    infer_instance

@[simp]
lemma toOfIsPullback_hom (sq : IsPullback g' f' f g) (c : Compactification f.left)
    (c' : Compactification f'.left) (h : c'.overObj ⟶ c.overObj)
    (hi : IsPullback g' c'.overI c.overI h) (hp : IsPullback h c'.overG c.overG g) :
    (toOfIsPullback sq c c' h hi hp).hom = toOfIsPullbackHom sq c c' h hp :=
  rfl

end OverRefinement

end AlgebraicGeometry.Compactification
