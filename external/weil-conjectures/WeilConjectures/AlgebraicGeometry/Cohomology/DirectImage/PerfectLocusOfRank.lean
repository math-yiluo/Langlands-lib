/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.BaseChange
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectLocus
import WeilConjectures.AlgebraicGeometry.HigherDirectImageDerivedModel
import WeilConjectures.AlgebraicGeometry.DerivedPullbackSingleCohomology

/-!
# Local freeness of the higher direct images on the perfect locus

Over the rank-`r` perfect locus the higher direct images are finite locally free of rank `r`
and their formation commutes with base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

section Coherence

variable [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation]

/-- **Cohomology and base change on the perfect locus.** In the situation of
`AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback`, the `i`-th higher
direct image commutes with the base change: `R^i f'_* ℱ' ≅ g^* R^i f_* ℱ`.

Locally on `U_i`, `R f_* ℱ` is a finite locally free module placed in degree `i`, and its
formation commutes with base change.

The isomorphism is only asserted to exist: it is not stated to be the canonical base-change map,
which is not available (see
`AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`).

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem nonempty_higherDirectImage_iso_pullback_of_isPullback (hℱ : ℱ.IsFlatOver f) {i : ℕ}
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g)
    (hg : Set.range g.base ⊆ ℱ.perfectLocus f i) :
    Nonempty ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ) ≅
      (Modules.pullback g).obj ((higherDirectImage f i).obj ℱ)) := by
  let (Y : Scheme.{u}) :
      HasDerivedCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
    HasDerivedCategory.standard _
  obtain ⟨E, hneg, hcoh, hbc⟩ := exists_derived_model_higherDirectImage f ℱ hℱ
  obtain ⟨e⟩ := nonempty_homology_derivedPullback_iso_of_locally_single g E i hneg (by
    intro t ht
    obtain ⟨U, htU, hU⟩ := exists_mem_isFiniteLocallyFreeInDegree_restrict f ℱ hℱ
      (𝟙 T) (𝟙 X) f (IsPullback.of_horiz_isIso ⟨by simp⟩) t
      (r := ℱ.hFiber f i t) ⟨hg ht, rfl⟩
    refine ⟨U, htU, ℱ.hFiber f i t, ?_⟩
    have ec q := (restrictFunctor U.ι).mapIso (hcoh q).some
    have eid := (Modules.pullbackId X).app ℱ
    have eh q := (restrictFunctor U.ι).mapIso ((higherDirectImage f q).mapIso eid)
    refine ⟨fun q hq ↦ (hU.isZero q hq).of_iso (ec q ≪≫ (eh q).symm), ?_⟩
    have := hU.isFiniteLocallyFreeOfRank
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso ((eh i) ≪≫ (ec i).symm))
  exact ⟨(hbc g g' f' sq i).some.symm ≪≫ e ≪≫
    (Modules.pullback g).mapIso (hcoh i).some⟩

/-- **Local freeness in degree `i` after base change to the perfect locus.** In the situation of
`AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback`, if the image of `g`
lies in the rank-`r` perfect locus `U_{i,r}`, then the higher direct image `R^i f'_* ℱ'` is
finite locally free of rank `r`.

This also follows from
`AlgebraicGeometry.Scheme.Modules.nonempty_higherDirectImage_iso_pullback_of_isPullback`, the
case of the inclusion of `U_{i,r}`, and the stability of finite local freeness of rank `r`
under pullback, which is not available.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback (hℱ : ℱ.IsFlatOver f)
    {i r : ℕ} {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g)
    (hg : Set.range g.base ⊆ ℱ.perfectLocusOfRank f i r) :
    ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank r := by
  choose V hV h using fun t' ↦ exists_mem_isFiniteLocallyFreeInDegree_restrict f ℱ hℱ g g' f' sq
    t' (hg ⟨t', rfl⟩)
  exact isFiniteLocallyFreeOfRank_of_iSup_eq_top _ V (eq_top_iff.2 fun t' _ ↦
    TopologicalSpace.Opens.mem_iSup.2 ⟨t', hV t'⟩) fun t' ↦ (h t').isFiniteLocallyFreeOfRank

/-- **The `i`-th higher direct image is finite locally free over the perfect locus.** Over an
open subscheme `U` of `T` contained in the rank-`r` perfect locus `U_{i,r}`, the higher direct
image `R^i f_* ℱ|_U` is finite locally free of rank `r`. This is the case of the inclusion of
`U` in
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem isFiniteLocallyFreeOfRank_higherDirectImage_restrict (hℱ : ℱ.IsFlatOver f) (i r : ℕ)
    (U : T.Opens)
    (hU : ↑U ⊆ {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r}) :
    (((higherDirectImage f i).obj ℱ).restrict U.ι).IsFiniteLocallyFreeOfRank r := by
  have := isGrothendieckAbelian (f ⁻¹ᵁ U).toScheme
  have sq : IsPullback (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι := (isPullback_morphismRestrict f U).flip
  obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ U.ι _ _ sq i
  have := isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback f ℱ hℱ U.ι _ _ sq
    (by rw [Scheme.Opens.range_ι]; exact hU)
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e

/-- **Base change detects the rank-`r` perfect locus.** Let `f' : X' ⟶ T'` and `g' : X' ⟶ X` be
the base change of `f` along `g : T' ⟶ T`, in the cartesian square `sq`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
with `ℱ'` the pullback of `ℱ` to `X'`. If `R f'_* ℱ'` is a finite locally free module of rank `r`
placed in degree `i`, then the image of `g` lies in the rank-`r` perfect locus `U_{i,r}`.

Locally on `T'`, `R f'_* ℱ'` is computed by the pullback `g^* P` of the bounded complex of finite
free modules of `AlgebraicGeometry.Scheme.Modules.exists_isFiniteFreeComplex_higherDirectImage`.
A bounded complex of finite free modules whose cohomology is finite locally free and
concentrated in degree `i` is locally homotopy equivalent to that cohomology placed in degree
`i`, so its fibre at a point `t'` of `T'` has cohomology of dimension `r` in degree `i` only.
This gives `h^q_{ℱ'}(t') = 0` for `q ≠ i` and `h^i_{ℱ'}(t') = r`, and these are the fibre
dimensions of `ℱ` at `g t'` by
`AlgebraicGeometry.Scheme.Modules.hFiber_pullback_of_isPullback`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem range_subset_perfectLocusOfRank_of_isPullback (hℱ : ℱ.IsFlatOver f) {i r : ℕ}
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g)
    (h₀ : ∀ q ≠ i, IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)))
    (h₁ : ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank
      r) :
    Set.range g.base ⊆ ℱ.perfectLocusOfRank f i r := by
  rintro _ ⟨t', rfl⟩
  obtain ⟨U, P, d, hsU, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ (g.base t')
  obtain ⟨UP, hUP⟩ := hP.exists_opens_range_subset_iff i r
  obtain ⟨gs, hgs⟩ := exists_comp_ι_eq_fromSpecResidueField hsU
  rw [← isFiniteLocallyFreeInDegree_homology_pullback_iff f ℱ hP hbc gs hgs i r]
  refine (hUP gs).1 ?_
  -- the base change of `P` to `V = g⁻¹ U` computes `R f'_* ℱ'` there
  let V := g ⁻¹ᵁ U
  have hgV : Set.range (V.ι ≫ g).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨w, rfl⟩
    exact ⟨⟨_, w.2⟩, rfl⟩
  let gV := IsOpenImmersion.lift U.ι (V.ι ≫ g) hgV
  have hgV' : gV ≫ U.ι = V.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have e q := (nonempty_restrict_higherDirectImage_iso_homology f ℱ hbc g g' f' sq V gV hgV' q).some
  have hV : Set.range gV.base ⊆ UP := (hUP gV).2
    ⟨fun q hq ↦ ((restrictFunctor V.ι).map_isZero (h₀ q hq)).of_iso (e q).symm,
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (e i)⟩
  rintro _ ⟨x, rfl⟩
  have : gs.base x = gV.base ⟨t', hsU⟩ := by
    refine U.ι.isOpenEmbedding.injective ?_
    rw [← Scheme.Hom.comp_apply, hgs, ← Scheme.Hom.comp_apply, hgV']
    exact (Scheme.range_fromSpecResidueField (g.base t')).subset ⟨x, rfl⟩
  rw [this]
  exact hV ⟨_, rfl⟩

/-- **Functorial characterisation of the rank-`r` perfect locus.** In the situation of
`AlgebraicGeometry.Scheme.Modules.range_subset_perfectLocusOfRank_of_isPullback`, the image of
`g` lies in `U_{i,r}` if and only if `R f'_* ℱ'` is a finite locally free module of rank `r`
placed in degree `i`: the higher direct images `R^q f'_* ℱ'` vanish for `q ≠ i` and
`R^i f'_* ℱ'` is finite locally free of rank `r`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem range_subset_perfectLocusOfRank_iff (hℱ : ℱ.IsFlatOver f) (i r : ℕ)
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g) :
    Set.range g.base ⊆ ℱ.perfectLocusOfRank f i r ↔
      (∀ q ≠ i, IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ))) ∧
        ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank r :=
  ⟨fun hg ↦ ⟨fun _ hq ↦ isZero_higherDirectImage_of_isPullback f ℱ hℱ g g' f' sq
      (hg.trans (perfectLocusOfRank_subset ℱ f i r)) hq,
    isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback f ℱ hℱ g g' f' sq hg⟩,
   fun h ↦ range_subset_perfectLocusOfRank_of_isPullback f ℱ hℱ g g' f' sq h.1 h.2⟩

/-- **Base change detects `U_{i,r}`.** In the situation of
`AlgebraicGeometry.Scheme.Modules.range_subset_perfectLocusOfRank_iff`, the image of `g` lies in
the locus of points at which the fibre cohomology vanishes outside degree `i` and has dimension
`r` in degree `i` if and only if `R^q f'_* ℱ'` vanishes for `q ≠ i` and `R^i f'_* ℱ'` is finite
locally free of rank `r`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem range_subset_setOf_hFiber_eq_iff (hℱ : ℱ.IsFlatOver f) (i r : ℕ)
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g) :
    Set.range g.base ⊆ {t : T | (∀ q ≠ i, ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r} ↔
      (∀ q ≠ i, IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ))) ∧
        ((higherDirectImage f' i).obj ((Modules.pullback g').obj ℱ)).IsFiniteLocallyFreeOfRank r :=
  range_subset_perfectLocusOfRank_iff f ℱ hℱ i r g g' f' sq

/-- **The open locus where `R f_* ℱ` is finite locally free in one degree.** With `f : X ⟶ T`
proper of finite presentation, `ℱ` an `𝒪_X`-module of finite presentation which is flat over `T`,
and `i r : ℕ`, there is an open subscheme `U` of `T`, namely `U_{i,r}`, such that a morphism
`g : T' ⟶ T` factors through `U` if and only if `R f'_* ℱ'` is a finite locally free module of
rank `r` placed in degree `i` [Stacks, Tag 0B9S].

Here `f' : X' ⟶ T'` and `g' : X' ⟶ X` are the base change of `f` along `g`, and `ℱ'` is the
pullback of `ℱ` to `X'`. The set `U_{i,r}` is open by
`AlgebraicGeometry.Scheme.Modules.isOpen_perfectLocusOfRank`, and the factorisation criterion is
`AlgebraicGeometry.Scheme.Modules.range_subset_perfectLocusOfRank_iff`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--3`) 
(blueprint: lemma-coherent-base-change-invertible-sheaves--3)
-/
theorem exists_opens_range_subset_iff_isFiniteLocallyFreeInDegree (hℱ : ℱ.IsFlatOver f)
    (i r : ℕ) :
    ∃ U : T.Opens, (U : Set T) = ℱ.perfectLocusOfRank f i r ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f g →
        (Set.range g.base ⊆ U ↔ IsFiniteLocallyFreeInDegree
          (fun q ↦ (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) i r) :=
  ⟨⟨_, isOpen_perfectLocusOfRank f ℱ hℱ i r⟩, rfl, fun g g' f' _ sq ↦
    (range_subset_perfectLocusOfRank_iff f ℱ hℱ i r g g' f' sq).trans
      ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩⟩

end Coherence

end AlgebraicGeometry.Scheme.Modules
