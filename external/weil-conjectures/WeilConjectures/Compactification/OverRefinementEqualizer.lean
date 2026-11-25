/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.OverRefinementBaseChange

/-!

# Composition and equalizers of refinements of compactifications over a base scheme

Let `f : X ⟶ Y` be a morphism of `Over S`. This file records two constructions on the
refinements `Compactification.OverRefinement` of compactifications of `f.left` (proper morphisms
over `Y` with cartesian square over `X`):

* `Compactification.OverRefinement.trans`: the composite of two refinements, whose square is
  the horizontal pasting of the two cartesian squares;
* `Compactification.OverRefinement.eqLocus`: for two refinements `r r' : c → c₁`, the
  compactification `X ⟶ E ⟶ Y` given by the equalizer `E ⊆ c.Z` of `r.hom` and `r'.hom` (the
  pullback of the diagonal of `c₁.Z ⟶ Y`, a closed immersion as `c₁.Z` is separated over `Y`),
  together with the refinement `OverRefinement.eqLocusRefinement r r' : eqLocus r r' → c`
  equalizing `r` and `r'` (`OverRefinement.eqLocusRefinement_hom_comp`). The square over `X`
  is cartesian since `E ⟶ c.Z` is a monomorphism through which `c.i` factors.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

variable {S : Scheme.{u}} {X Y : Over S} {f : X ⟶ Y}

namespace OverRefinement

variable {c c₁ c₂ : Compactification f.left}

/-- The composite of two refinements of compactifications in `Over S`. -/
@[simps]
noncomputable def trans (r : OverRefinement c c₁) (s : OverRefinement c₁ c₂) :
    OverRefinement c c₂ where
  hom := r.hom ≫ s.hom
  hom_overG := by rw [Category.assoc, s.hom_overG, r.hom_overG]
  isPullback := r.isPullback.paste_horiz s.isPullback
  isProper := by
    have := r.isProper
    have := s.isProper
    rw [Over.comp_left]
    infer_instance

variable (r r' : OverRefinement c c₁)

lemma hom_left_comp_g : r.hom.left ≫ c₁.g = c.g :=
  congrArg CommaMorphism.left r.hom_overG

/-- The equalizer of the ambient morphisms of two refinements `r r' : c → c₁`: the pullback of
the diagonal of `c₁.g` along `(r.hom, r'.hom) : c.Z ⟶ c₁.Z ×_Y c₁.Z`. -/
noncomputable def eqLocusZ : Scheme.{u} :=
  pullback (pullback.diagonal c₁.g)
    (pullback.lift r.hom.left r'.hom.left (by rw [r.hom_left_comp_g, r'.hom_left_comp_g]))

/-- The closed immersion of the equalizer of `r.hom` and `r'.hom` into `c.Z`. -/
noncomputable def eqLocusι : eqLocusZ r r' ⟶ c.Z :=
  pullback.snd _ _

instance : IsClosedImmersion (eqLocusι r r') := by
  unfold eqLocusι
  infer_instance

instance : Mono (eqLocusι r r') := by
  unfold eqLocusι
  infer_instance

lemma eqLocusι_comp : eqLocusι r r' ≫ r.hom.left = eqLocusι r r' ≫ r'.hom.left := by
  have h := pullback.condition (f := pullback.diagonal c₁.g)
    (g := pullback.lift r.hom.left r'.hom.left (by rw [r.hom_left_comp_g, r'.hom_left_comp_g]))
  have h₁ := congrArg (· ≫ pullback.fst c₁.g c₁.g) h
  have h₂ := congrArg (· ≫ pullback.snd c₁.g c₁.g) h
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, pullback.lift_fst,
    pullback.lift_snd] at h₁ h₂
  rw [eqLocusι, ← h₁, h₂]

lemma i_comp_hom_left : c.i ≫ r.hom.left = c₁.i := by
  simpa using r.isPullback_left.w.symm

/-- The open immersion of `X` into the equalizer of `r.hom` and `r'.hom`. -/
noncomputable def eqLocusI : X.left ⟶ eqLocusZ r r' :=
  pullback.lift c₁.i c.i (by
    apply pullback.hom_ext <;>
      simp [i_comp_hom_left])

@[reassoc (attr := simp)]
lemma eqLocusI_ι : eqLocusI r r' ≫ eqLocusι r r' = c.i :=
  pullback.lift_snd _ _ _

/-- The square of the open immersions of `X` into the equalizer of `r.hom` and `r'.hom` and
into `c.Z` is cartesian, the inclusion of the equalizer being a monomorphism. -/
lemma isPullback_eqLocusI : IsPullback (𝟙 X.left) (eqLocusI r r') c.i (eqLocusι r r') := by
  have := (IsPullback.of_horiz_isIso (fst := 𝟙 X.left) (snd := eqLocusI r r')
    (f := eqLocusI r r') (g := 𝟙 _) ⟨by simp⟩).paste_vert (IsKernelPair.id_of_mono (eqLocusι r r'))
  simpa using this

instance : IsOpenImmersion (eqLocusI r r') :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_eqLocusI r r')
    c.isOpenImmersion

/-- The compactification `X ⟶ E ⟶ Y` of `f.left` given by the equalizer `E` of the ambient
morphisms of two refinements `r r' : c → c₁`. -/
noncomputable def eqLocus : Compactification f.left where
  Z := eqLocusZ r r'
  g := eqLocusι r r' ≫ c.g
  i := eqLocusI r r'
  comm := by
    rw [eqLocusI_ι_assoc]
    exact c.comm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The refinement of `c` by the equalizer compactification `eqLocus r r'`. -/
noncomputable def eqLocusRefinement : OverRefinement (eqLocus r r') c :=
  overRefinementOfRefinement (c := eqLocus r r') (c₁ := c)
    { hom := eqLocusι r r'
      i_hom := eqLocusI_ι r r'
      hom_g := rfl }
    (isPullback_eqLocusI r r')

/-- The refinement `eqLocusRefinement r r'` equalizes `r` and `r'`. -/
lemma eqLocusRefinement_hom_comp :
    (eqLocusRefinement r r').hom ≫ r.hom = (eqLocusRefinement r r').hom ≫ r'.hom :=
  Over.OverMorphism.ext (eqLocusι_comp r r')

end OverRefinement

end AlgebraicGeometry.Compactification
