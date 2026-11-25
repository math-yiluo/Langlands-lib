/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Compactification.Comp
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.Compactification.Over
import WeilConjectures.Compactification.CommonRefinement
import WeilConjectures.Compactification.Comp
import WeilConjectures.Compactification.Dense

/-!

# Refinements and composites of compactifications over a base scheme

Let `S` be a quasi-compact and quasi-separated scheme, and let `f : X ⟶ Y` be a morphism of
`Over S`, between objects whose structure morphisms are separated and of finite type. This file
records the two geometric inputs that make the lower shriek independent of the compactification
and compatible with composition.

* **Refinements.** A refinement of a compactification `c₁ = (X ⟶[i₁] Z₁ ⟶[p₁] Y)` of `f.left` by
  a compactification `c = (X ⟶[i] Z ⟶[p] Y)` is a proper morphism `h : Z ⟶ Z₁` over `Y` such that
  the square
  ```
  X --i--> Z
  |𝟙       |h
  v        v
  X --i₁-> Z₁
  ```
  is cartesian, that is `h⁻¹(X) = X` (`Compactification.OverRefinement`). Any two
  compactifications have a common refinement (`Compactification.exists_overRefinement`): the
  scheme-theoretic closure of the image of `X` in `Z₁ ×_Y Z₂`.
* **Composites.** For compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of `f.left` and
  `c' = (Y ⟶[j] Z' ⟶[q] T)` of `g.left`, the morphism `p ≫ j : Z ⟶ Z'` has a compactification
  `d = (Z ⟶[i'] W ⟶[p'] Z')` whose square
  ```
  Z --i'--> W
  |p        |p'
  v         v
  Y --j---> Z'
  ```
  is cartesian (`Compactification.exists_isPullback_overG_overI`): the scheme-theoretic closure
  of `Z` in any compactification of `p ≫ j`. Then `X ⟶[i ≫ i'] W ⟶[p' ≫ q] T` is a
  compactification of `(f ≫ g).left` (`Compactification.overComp`).

## Proofs

* The common refinement is `Compactification.inf c₁ c₂`, whose squares over `X` are cartesian
  by `Compactification.isPullback_infFst` and `Compactification.isPullback_infSnd`; a refinement
  of compactifications with cartesian square over `X` is a refinement in `Over S`
  (`Compactification.overRefinementOfRefinement`).
* For the composite, `d` is a dense compactification of `p ≫ j`
  (`AlgebraicGeometry.exists_isDense_compactification`). Its square is cartesian by
  `Compactification.isPullback_of_isProper_of_isSchemeTheoreticallyDominant`: for `p` proper,
  `j` an open immersion and `e` a compactification of `p ≫ j` whose open immersion is
  quasi-compact and scheme-theoretically dominant, the open immersion `Z ⟶ p'⁻¹(Y)` of the
  restriction `e.restrict` is a closed immersion (`Z` is proper over `Y`) and
  scheme-theoretically dominant (restriction of a dominant morphism to an open), hence an
  isomorphism (`Compactification.isIso_restrict_i`).

Cartesian squares of schemes give cartesian squares in `Over S`, the forgetful functor
reflecting pullbacks.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Compactification

section Restrict

variable {X Y W : Scheme.{u}} {f : X ⟶ Y} {m : Y ⟶ W} [IsOpenImmersion m]

/-- Let `f` be proper, `m` an open immersion and `e` a compactification of `f ≫ m` whose open
immersion is quasi-compact and scheme-theoretically dominant. Then the open immersion of the
restriction of `e` over `Y` is an isomorphism: it is a closed immersion, being an open immersion
into a compactification of a proper morphism, and it is scheme-theoretically dominant, being the
restriction of `e.i` to an open subscheme. -/
theorem isIso_restrict_i [IsProper f] (e : Compactification (f ≫ m))
    [IsSchemeTheoreticallyDominant e.i] [QuasiCompact e.i] : IsIso e.restrict.i := by
  have : IsClosedImmersion e.restrict.i :=
    e.restrict.isClosedImmersion_openImmersion inferInstance
  have : QuasiCompact (e.restrict.i ≫ pullback.fst e.g m) := by
    rw [restrict_i_fst]
    infer_instance
  have : IsSchemeTheoreticallyDominant (e.restrict.i ≫ pullback.fst e.g m) := by
    rw [restrict_i_fst]
    infer_instance
  have : IsSchemeTheoreticallyDominant e.restrict.i := .of_comp _ (pullback.fst e.g m)
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr e.restrict.i.ker_eq_bot

/-- **A dense compactification of a proper morphism followed by an open immersion is cartesian**:
for `f : X ⟶ Y` proper, `m : Y ⟶ W` an open immersion and a compactification
`X ⟶[e.i] e.Z ⟶[e.g] W` of `f ≫ m` whose open immersion is quasi-compact and
scheme-theoretically dominant, the square
```
X --e.i--> e.Z
|f          |e.g
v           v
Y ---m----> W
```
is cartesian, that is `e.g⁻¹(Y) = X`. -/
theorem isPullback_of_isProper_of_isSchemeTheoreticallyDominant [IsProper f]
    (e : Compactification (f ≫ m)) [IsSchemeTheoreticallyDominant e.i] [QuasiCompact e.i] :
    IsPullback f e.i m e.g := by
  have := e.isIso_restrict_i
  refine e.isPullback_restrict.of_iso (asIso e.restrict.i).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [e.restrict.comm]
  · simp

end Restrict

variable {S : Scheme.{u}} {X Y : Over S} {f : X ⟶ Y}

/-- A *refinement* of a compactification `c₁ = (X ⟶[i₁] Z₁ ⟶[p₁] Y)` of `f.left` by a
compactification `c = (X ⟶[i] Z ⟶[p] Y)`: a proper morphism `h : Z ⟶ Z₁` of `Over S` over `Y`
whose square with `i` and `i₁` is cartesian, that is `h⁻¹(X) = X`. -/
structure OverRefinement (c c₁ : Compactification f.left) where
  /-- The proper morphism `h : Z ⟶ Z₁` between the compactifications. -/
  hom : c.overObj ⟶ c₁.overObj
  hom_overG : hom ≫ c₁.overG = c.overG
  isPullback : IsPullback (𝟙 X) c.overI c₁.overI hom
  isProper : IsProper hom.left

/-- A refinement `r` of compactifications of `f.left` whose square over `X` is cartesian, as a
refinement of compactifications in `Over S`. -/
noncomputable def overRefinementOfRefinement {c c₁ : Compactification f.left}
    (r : c.Refinement c₁) (h : IsPullback (𝟙 X.left) c.i c₁.i r.hom) : OverRefinement c c₁ where
  hom := Over.homMk r.hom (by simp [overObj, reassoc_of% r.hom_g])
  hom_overG := Over.OverMorphism.ext r.hom_g
  isPullback := IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext h.w) h
  isProper := r.isProper

variable {T : Over S} {g : Y ⟶ T}

/-- The composite compactification `X ⟶[i ≫ i'] W ⟶[p' ≫ q] T` of `(f ≫ g).left`, for
compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of `f.left`, `c' = (Y ⟶[j] Z' ⟶[q] T)` of `g.left`,
and `d = (Z ⟶[i'] W ⟶[p'] Z')` of `p ≫ j`. -/
noncomputable def overComp (c : Compactification f.left) (c' : Compactification g.left)
    (d : Compactification (c.overG ≫ c'.overI).left) : Compactification (f ≫ g).left where
  Z := d.Z
  g := d.g ≫ c'.g
  i := c.i ≫ d.i
  comm := by
    have hd : c.g ≫ c'.i = d.i ≫ d.g := by simpa using d.comm
    calc (f ≫ g).left = (c.i ≫ c.g) ≫ c'.i ≫ c'.g := by
          rw [Over.comp_left, ← c.comm, ← c'.comm]
      _ = (c.i ≫ d.i) ≫ d.g ≫ c'.g := by
          simp only [Category.assoc]
          rw [reassoc_of% hd]
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The object `W` of the composite compactification `overComp c c' d` is the object of `d`, up
to the associativity of the structure morphism `W ⟶ Z' ⟶ T ⟶ S`. -/
noncomputable def overCompObjIso (c : Compactification f.left) (c' : Compactification g.left)
    (d : Compactification (c.overG ≫ c'.overI).left) :
    (overComp c c' d).overObj ≅ d.overObj :=
  Over.isoMk (Iso.refl _) (by simp [overComp, overObj])

@[reassoc (attr := simp)]
lemma overI_overCompObjIso_hom (c : Compactification f.left) (c' : Compactification g.left)
    (d : Compactification (c.overG ≫ c'.overI).left) :
    (overComp c c' d).overI ≫ (overCompObjIso c c' d).hom = c.overI ≫ d.overI := by
  ext
  simp [overCompObjIso, overComp]

@[reassoc (attr := simp)]
lemma overCompObjIso_hom_overG (c : Compactification f.left) (c' : Compactification g.left)
    (d : Compactification (c.overG ≫ c'.overI).left) :
    (overCompObjIso c c' d).hom ≫ d.overG ≫ c'.overG = (overComp c c' d).overG := by
  ext
  simp [overCompObjIso, overComp]

section Existence

/-- Any two compactifications `c₁` and `c₂` of `f.left` have a common refinement: the
scheme-theoretic closure `Z` of the image of `X` in `Z₁ ×_Y Z₂`, with the projections to `Z₁`
and `Z₂`. The immersion `X ⟶ Z₁ ×_Y Z₂` is an open immersion into its scheme-theoretic closure,
and the preimage of `X ⊆ Z₁` in `Z` is `X`, since `X` is closed in `X ×_Y Z₂` (`Z₂` is separated
over `Y`). -/
theorem exists_overRefinement [QuasiCompact X.hom] [IsSeparated Y.hom]
    (c₁ c₂ : Compactification f.left) :
    ∃ c : Compactification f.left, Nonempty (OverRefinement c c₁) ∧
      Nonempty (OverRefinement c c₂) := by
  have : QuasiCompact f.left := by
    have : QuasiCompact (f.left ≫ Y.hom) := by
      rw [Over.w]
      infer_instance
    exact .of_comp f.left Y.hom
  exact ⟨inf c₁ c₂, ⟨overRefinementOfRefinement _ (isPullback_infFst c₁ c₂).flip⟩,
    ⟨overRefinementOfRefinement _ (isPullback_infSnd c₁ c₂).flip⟩⟩

/-- For compactifications `c = (X ⟶[i] Z ⟶[p] Y)` of `f.left` and `c' = (Y ⟶[j] Z' ⟶[q] T)` of
`g.left`, the morphism `p ≫ j : Z ⟶ Z'` has a compactification `d = (Z ⟶[i'] W ⟶[p'] Z')`
whose square with `p` and `j` is cartesian: the scheme-theoretic closure `W` of `Z` in any
compactification of `p ≫ j`. Then `p'⁻¹(Y)` contains `Z` as an open subscheme which is proper,
hence closed, over `Y`, and schematically dense, so that `p'⁻¹(Y) = Z`. -/
theorem exists_isPullback_overG_overI [CompactSpace S] [QuasiSeparatedSpace S]
    [QuasiCompact Y.hom] [QuasiCompact T.hom] [IsSeparated T.hom] (c : Compactification f.left)
    (c' : Compactification g.left) :
    ∃ d : Compactification (c.overG ≫ c'.overI).left,
      IsPullback c.overG d.overI c'.overI d.overG := by
  have : QuasiCompact g.left := by
    have : QuasiCompact (g.left ≫ T.hom) := by
      rw [Over.w]
      infer_instance
    exact .of_comp g.left T.hom
  have : QuasiCompact c'.i := c'.quasiCompact_openImmersion inferInstance
  have : CompactSpace c'.Z := QuasiCompact.compactSpace_of_compactSpace (c'.g ≫ T.hom)
  have : QuasiSeparatedSpace c'.Z := quasiSeparatedSpace_of_quasiSeparated (c'.g ≫ T.hom)
  obtain ⟨d, hd⟩ := exists_isDense_compactification (c.g ≫ c'.i)
  have : IsSchemeTheoreticallyDominant d.i := hd
  have : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  exact ⟨d, IsPullback.of_map (Over.forget S) (Over.OverMorphism.ext d.comm)
    d.isPullback_of_isProper_of_isSchemeTheoreticallyDominant⟩

end Existence

end AlgebraicGeometry.Compactification
