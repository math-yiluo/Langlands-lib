/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Compactification.RefinementCategory

/-!
# Base change of refinements along a cartesian square

Let `hsq : IsPullback h u p t` be a cartesian square of schemes and let `r : c.Refinement d` be a
refinement of compactifications of `p`. Its base change
`r.ofIsPullback hsq : (c.ofIsPullback hsq).Refinement (d.ofIsPullback hsq)` is the refinement
`r.hom ×_T S : c.Z ×_T S ⟶ d.Z ×_T S`. If the square of `r` over the source of `p` is cartesian,
so is the square of its base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification.Refinement

variable {X Y S T : Scheme.{u}} {u : X ⟶ S} {p : Y ⟶ T} {h : X ⟶ Y} {t : S ⟶ T}
  {c d : Compactification p}

/-- **Base change of a refinement along a cartesian square**: the refinement
`r.hom ×_T S : c.Z ×_T S ⟶ d.Z ×_T S` of `d.ofIsPullback hsq` by `c.ofIsPullback hsq`. -/
@[simps]
noncomputable def ofIsPullback (hsq : IsPullback h u p t) (r : c.Refinement d) :
    (c.ofIsPullback hsq).Refinement (d.ofIsPullback hsq) where
  hom := pullback.map c.g t d.g t r.hom (𝟙 S) (𝟙 T) (by rw [r.hom_g, Category.comp_id])
    (by simp)
  i_hom := pullback.hom_ext (by simp [r.i_hom]) (by simp)
  hom_g := by simp

@[reassoc (attr := simp)]
lemma ofIsPullback_hom_fst (hsq : IsPullback h u p t) (r : c.Refinement d) :
    (r.ofIsPullback hsq).hom ≫ pullback.fst d.g t = pullback.fst c.g t ≫ r.hom := by
  simp

/-- The square of the base change of a refinement over its base change is cartesian:
```
c.Z ×_T S --(r.ofIsPullback hsq).hom--> d.Z ×_T S
|fst                                    |fst
c.Z ---------------r.hom-------------> d.Z
```
-/
theorem isPullback_ofIsPullback_hom (hsq : IsPullback h u p t) (r : c.Refinement d) :
    IsPullback (r.ofIsPullback hsq).hom (pullback.fst c.g t) (pullback.fst d.g t) r.hom := by
  refine IsPullback.of_right ?_ (ofIsPullback_hom_fst hsq r)
    (IsPullback.of_hasPullback d.g t).flip
  have : (r.ofIsPullback hsq).hom ≫ pullback.snd d.g t = pullback.snd c.g t := by simp
  rw [this, r.hom_g]
  exact (IsPullback.of_hasPullback c.g t).flip

/-- **Cartesianness over the source is stable under base change**: if the square of the
refinement `r` over `Y` is cartesian, then so is the square of `r.ofIsPullback hsq` over `X`. -/
theorem isPullback_ofIsPullback (hsq : IsPullback h u p t) (r : c.Refinement d)
    (hr : IsPullback c.i (𝟙 Y) r.hom d.i) :
    IsPullback (c.ofIsPullback hsq).i (𝟙 X) (r.ofIsPullback hsq).hom (d.ofIsPullback hsq).i := by
  have outer : IsPullback (𝟙 X) ((c.ofIsPullback hsq).i ≫ pullback.fst c.g t)
      ((d.ofIsPullback hsq).i ≫ pullback.fst d.g t) r.hom := by
    rw [ofIsPullback_i_fst, ofIsPullback_i_fst]
    exact (IsPullback.of_horiz_isIso (fst := 𝟙 X) (snd := h) (f := h) (g := 𝟙 Y)
      ⟨by simp⟩).paste_vert hr.flip
  exact (outer.of_bot (by rw [Category.id_comp, (r.ofIsPullback hsq).i_hom])
    (isPullback_ofIsPullback_hom hsq r)).flip

end AlgebraicGeometry.Compactification.Refinement
