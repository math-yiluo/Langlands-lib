/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ChowLemma
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Proper schemes over an affine base are dominated by projective ones

Let `f : X ⟶ Y` be a proper morphism with `Y` affine, but with no Noetherian or finite
presentation hypothesis. Then there are a proper surjective morphism `π : X̃ ⟶ X` and a closed
immersion `i : X̃ ⟶ ℙ(n; Y)` over `Y`, with `n` finite. We bundle such data into
`AlgebraicGeometry.ProjectiveDomination f`, prove that it exists
(`AlgebraicGeometry.ProjectiveDomination.nonempty_of_isAffine`) and that it is stable under base
change on `Y` (`AlgebraicGeometry.ProjectiveDomination.pullback`).

## Main definitions

- `AlgebraicGeometry.ProjectiveDomination f` — a proper surjection onto `X` from a closed
  subscheme of a projective space over `Y`, compatibly with `f`.
- `AlgebraicGeometry.ProjectiveDomination.pullback` — its base change along `Y' ⟶ Y`.

## Main statements

- `AlgebraicGeometry.ProjectiveDomination.nonempty_of_isAffine` — a proper morphism to an
  affine scheme admits a projective domination.

## Implementation notes

The proof never descends `X` itself. The separated finitely presented envelope `X ⟶ X'` of
`f` (Stacks Project Tag 01ZJ) descends to a separated finitely presented `X₀' ⟶ Y₀` over a
stage `Y₀` of a Noetherian approximation of `Y` (Stacks Project Tag 01ZQ). Chow's lemma over
the Noetherian `Y₀` (`AlgebraicGeometry.ChowModification`) dominates `X₀'` by a scheme
immersed into `ℙ(n; Y₀)`; we base change it to `X'`, restrict it to the closed subscheme `X`,
and the immersion obtained is closed since its source is proper over `Y`.

## References

* [Stacks, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
* [Stacks, Tag 0202](https://stacks.math.columbia.edu/tag/0202)

## Blueprint

The declarations of this file implement `lemma-weil-pbc-chow-factorization`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A **projective domination** of `f : X ⟶ Y`: a proper surjective morphism `π : X̃ ⟶ X` and a
closed immersion `i : X̃ ⟶ ℙ(n; Y)` with `n` finite, such that

```
          i
   X̃ ------> ℙ(n; Y)
   |            |
 π |            | ↘
   ↓            ↓
   X ---------> Y
          f
```

commutes. (Blueprint `theorem-chow-s-lemma-projective-form--1`.) -/
structure ProjectiveDomination {X Y : Scheme.{u}} (f : X ⟶ Y) where
  /-- the dominating scheme `X̃` -/
  X' : Scheme.{u}
  /-- the proper surjection `X̃ ⟶ X` -/
  π : X' ⟶ X
  [isProper_π : IsProper π]
  [surjective_π : Surjective π]
  /-- the index type of the homogeneous coordinates of the ambient projective space -/
  n : Type u
  [finite_n : Finite n]
  /-- the closed immersion of `X̃` into the projective space `ℙ(n; Y)` -/
  i : X' ⟶ ℙ(n; Y)
  [isClosedImmersion_i : IsClosedImmersion i]
  /-- the closed immersion is a morphism over `Y` -/
  w : i ≫ ℙ(n; Y) ↘ Y = π ≫ f

attribute [instance] ProjectiveDomination.isProper_π ProjectiveDomination.surjective_π
  ProjectiveDomination.finite_n ProjectiveDomination.isClosedImmersion_i

namespace ProjectiveDomination

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- **Projective dominations are stable under base change**: the base change of a projective
domination of `f : X ⟶ Y` along `g : Y' ⟶ Y` is a projective domination of
`X ×_Y Y' ⟶ Y'`. The closed immersion into `ℙ(n; Y')` is the base change of the given one along
`ℙ(n; Y') ⟶ ℙ(n; Y)`. (Blueprint `theorem-chow-s-lemma-projective-form--1`, base change part.) -/
noncomputable def pullback (D : ProjectiveDomination f) {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    ProjectiveDomination (Limits.pullback.snd f g) :=
  have h : IsPullback (Limits.pullback.fst (D.π ≫ f) g) (Limits.pullback.snd (D.π ≫ f) g)
      (D.i ≫ ℙ(D.n; Y) ↘ Y) g := by
    rw [D.w]
    exact IsPullback.of_hasPullback _ _
  have hw : Limits.pullback.snd (D.π ≫ f) g ≫ g =
      (Limits.pullback.fst (D.π ≫ f) g ≫ D.i) ≫ ℙ(D.n; Y) ↘ Y := by
    rw [Category.assoc, D.w, Limits.pullback.condition]
  have : IsClosedImmersion (ProjectiveSpace.liftBaseChange _ _ hw) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_liftBaseChange _ h hw)
      inferInstance
  have hπ : IsPullback (Limits.pullback.map (D.π ≫ f) g f g D.π (𝟙 _) (𝟙 _) (by simp)
      (by simp)) (Limits.pullback.fst (D.π ≫ f) g) (Limits.pullback.fst f g) D.π := by
    refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback f g).flip
    simpa using (IsPullback.of_hasPullback (D.π ≫ f) g).flip
  have : IsProper (Limits.pullback.map (D.π ≫ f) g f g D.π (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
    MorphismProperty.of_isPullback hπ.flip inferInstance
  have : Surjective (Limits.pullback.map (D.π ≫ f) g f g D.π (𝟙 _) (𝟙 _) (by simp)
      (by simp)) :=
    MorphismProperty.of_isPullback hπ.flip inferInstance
  { X' := Limits.pullback (D.π ≫ f) g
    π := Limits.pullback.map (D.π ≫ f) g f g D.π (𝟙 _) (𝟙 _) (by simp) (by simp)
    n := D.n
    i := ProjectiveSpace.liftBaseChange _ _ hw
    w := by simp }

/-- **Proper schemes over an affine base are dominated by projective ones.** Let `f : X ⟶ Y`
be proper with `Y` affine; no Noetherian or finite presentation hypothesis is imposed. Then
there are a proper surjection `π : X̃ ⟶ X` and a closed immersion `i : X̃ ⟶ ℙ(n; Y)` over `Y`,
with `n` finite.

The separated finitely presented envelope `X ⟶ X'` of `f` (Stacks Project Tag 01ZJ) is the base
change of a separated finitely presented `X₀' ⟶ Y₀` over a stage `Y₀` of the Noetherian
approximation of `Y` (Stacks Project Tag 01ZQ). Chow's lemma over `Y₀` gives a proper surjection
`π₀ : X₀'' ⟶ X₀'` and an immersion `X₀'' ⟶ ℙ(n; Y₀)`; base changing `π₀` along `X' ⟶ X₀'` and
then along `X ⟶ X'` gives `π`, and the induced morphism to `ℙ(n; Y)` is an immersion whose
source is proper over `Y`, hence a closed immersion.
(Blueprint `theorem-chow-s-lemma-projective-form--1`.) -/
theorem nonempty_of_isAffine [IsAffine Y] [IsProper f] : Nonempty (ProjectiveDomination f) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  -- Step 1: the separated finitely presented envelope `X ⟶ X'` of `f`.
  obtain ⟨X', ι, g, hι, hg₁, hg₂, hg₃, hιg⟩ :=
    f.exists_isClosedImmersion_isSeparated_locallyOfFinitePresentation
  -- Step 2: `g` descends to a stage `Y₀` of the Noetherian approximation of `Y`.
  let N := Scheme.NoetherianApproximation.ofIsAffine Y
  obtain ⟨k, X₀, p, hp₁, hp₂, hp₃, h, H⟩ :=
    Scheme.exists_isPullback_of_finitePresentation_of_isSeparated N.isLimit g
  -- Step 3: Chow's lemma for `p` over the Noetherian scheme `Y₀`.
  have : LocallyOfFiniteType p := inferInstance
  let π₀ := ChowModification.modificationMap p
  let e₀ := ChowModification.toProjectiveSpace p
  -- Step 4: base change of `π₀` along `h : X' ⟶ X₀`.
  have H' : IsPullback (Limits.pullback.fst π₀ h) (Limits.pullback.snd π₀ h ≫ g)
      (e₀ ≫ ℙ(ChowModification.index p; N.D.obj k) ↘ N.D.obj k) (N.π.app k) := by
    rw [ChowModification.toProjectiveSpace_over]
    exact (IsPullback.of_hasPullback π₀ h).paste_vert H
  have hw : (Limits.pullback.snd π₀ h ≫ g) ≫ N.π.app k =
      (Limits.pullback.fst π₀ h ≫ e₀) ≫
        ℙ(ChowModification.index p; N.D.obj k) ↘ N.D.obj k := H'.w.symm.trans (by simp)
  let i'' := ProjectiveSpace.liftBaseChange _ _ hw
  have : IsImmersion i'' :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_liftBaseChange _ H' hw)
      inferInstance
  -- Step 5: restriction to the closed subscheme `X` of `X'`.
  let π := Limits.pullback.snd (Limits.pullback.snd π₀ h) ι
  let i := Limits.pullback.fst (Limits.pullback.snd π₀ h) ι ≫ i''
  have hi : i ≫ ℙ(ChowModification.index p; Y) ↘ Y = π ≫ f := by
    simp only [i, π, i'', Category.assoc, ProjectiveSpace.liftBaseChange_over]
    rw [Limits.pullback.condition_assoc, hιg]
  -- Step 6: `i` is a closed immersion, its source being proper over `Y`.
  have : IsProper (i ≫ ℙ(ChowModification.index p; Y) ↘ Y) := by
    rw [hi]
    infer_instance
  have : IsProper i := .of_comp _ (ℙ(ChowModification.index p; Y) ↘ Y)
  have : IsClosedImmersion i := .of_universallyClosed _
  exact ⟨{ X' := Limits.pullback (Limits.pullback.snd π₀ h) ι
           π := π
           n := ChowModification.index p
           i := i
           w := hi }⟩

end ProjectiveDomination

end AlgebraicGeometry
