/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Semicontinuity

/-!
# The perfect locus of the higher direct images

On an open over which `R f_* ℱ` is computed by a finite free complex, the higher direct images
at the points of the perfect locus are locally free and commute with base change.
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

omit [LocallyOfFinitePresentation f] [HasInjectiveResolutions X.Modules] in
/-- At a point `s` of an open `U` of the base over which `R f_* ℱ` is computed by a bounded
complex `P` of finite free modules compatibly with base change, the fibre `P ⊗ κ(s)` is a finite
locally free module of rank `r` placed in degree `i` if and only if `s` lies in the rank-`r`
perfect locus `U_{i,r}`. -/
theorem isFiniteLocallyFreeInDegree_homology_pullback_iff {U : T.Opens}
    {P : CochainComplex U.toScheme.Modules ℤ} {d : ℕ} (hP : IsFiniteFreeComplex P d)
    (hbc : ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)))
    {s : T} (g : Spec (T.residueField s) ⟶ U.toScheme) (hg : g ≫ U.ι = T.fromSpecResidueField s)
    (i r : ℕ) :
    IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (((Modules.pullback g).mapHomologicalComplex _).obj P).homology q) i r ↔
      s ∈ ℱ.perfectLocusOfRank f i r := by
  have hκ : IsField (T.residueField s) := Field.toIsField _
  have (q : ℕ) := finite_moduleSpecΓFunctor_obj_homology_pullback hP.exists_iso_free hκ g q
  simp only [mem_perfectLocusOfRank, mem_perfectLocus, hFiber_eq_finrank_homology f ℱ hbc g hg]
  refine ⟨fun ⟨hz, hl⟩ ↦ ⟨fun q hq ↦ (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hκ _).1
      (hz q hq), (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj hκ _ r).1 hl⟩,
    fun ⟨hz, hl⟩ ↦ ⟨fun q hq ↦ (isZero_iff_finrank_moduleSpecΓFunctor_obj_eq_zero hκ _).2
      (hz q hq), (isFiniteLocallyFreeOfRank_iff_finrank_moduleSpecΓFunctor_obj hκ _ r).2 hl⟩⟩

omit [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation] in
/-- In the situation of `isFiniteLocallyFreeInDegree_homology_pullback_iff`, let `f' : X' ⟶ T'`
be the base change of `f` along `g : T' ⟶ T`, and `V` an open of `T'` which `g` maps into `U`.
Then the restriction of `R^q f'_* ℱ'` to `V` is the cohomology of the pullback of `P` to `V`. -/
theorem nonempty_restrict_higherDirectImage_iso_homology {U : T.Opens}
    {P : CochainComplex U.toScheme.Modules ℤ}
    (hbc : ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj P).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)))
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g) (V : T'.Opens)
    (gV : V.toScheme ⟶ U.toScheme) (hgV : gV ≫ U.ι = V.ι ≫ g) (q : ℕ) :
    Nonempty (((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)).restrict V.ι ≅
      (((Modules.pullback gV).mapHomologicalComplex _).obj P).homology q) := by
  have := isGrothendieckAbelian (f' ⁻¹ᵁ V).toScheme
  have sq' : IsPullback (f' ⁻¹ᵁ V).ι (f' ∣_ V) f' V.ι := (isPullback_morphismRestrict f' V).flip
  obtain ⟨e₁⟩ := nonempty_higherDirectImage_iso_restrict f' ((Modules.pullback g').obj ℱ) V.ι _ _
    sq' q
  have sq'' : IsPullback ((f' ⁻¹ᵁ V).ι ≫ g') (f' ∣_ V) f (gV ≫ U.ι) := by
    rw [hgV]
    exact sq'.paste_horiz sq
  obtain ⟨e₂⟩ := hbc gV _ _ sq'' q
  exact ⟨e₁.symm ≪≫ (higherDirectImage (f' ∣_ V) q).mapIso
    ((Modules.pullbackComp _ _).app ℱ) ≪≫ e₂.symm⟩

omit [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation] in
/-- Let `f' : X' ⟶ T'` be the base change of `f` along `g : T' ⟶ T`, and `V` an open of `T'`.
An isomorphism `E ≅ R (f' ∣_ V)_* ℱ_V` in `D(𝒪_V)`, where `ℱ_V` is the pullback of `ℱ` to
`f'⁻¹(V)`, gives `(R f'_* ℱ')|_V ≅ E`: restriction to `V` commutes with `R f'_*`
(`AlgebraicGeometry.Scheme.Modules.derivedPushforwardIsoRestrict`). -/
noncomputable def restrictDerivedPushforwardIso {T' X' : Scheme.{u}} (g' : X' ⟶ X)
    (f' : X' ⟶ T') (V : T'.Opens) {E : DerivedCategory V.toScheme.Modules}
    (e : E ≅ (derivedPushforward (f' ∣_ V)).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((Modules.pullback ((f' ⁻¹ᵁ V).ι ≫ g')).obj ℱ))) :
    (restrictFunctor V.ι).mapDerivedCategory.obj ((derivedPushforward f').obj
        ((DerivedCategory.singleFunctor _ 0).obj ((Modules.pullback g').obj ℱ))) ≅ E :=
  (derivedPushforwardIsoRestrict f' ((Modules.pullback g').obj ℱ) V.ι _ _
      (isPullback_morphismRestrict f' V).flip).symm ≪≫
    (derivedPushforward (f' ∣_ V)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso ((Modules.pullbackComp _ _).app ℱ)) ≪≫ e.symm

omit [IsProper f] [LocallyOfFinitePresentation f] [QuasiCompact f]
  [HasInjectiveResolutions X.Modules] [ℱ.IsFinitePresentation] in
/-- The derived form of `nonempty_restrict_higherDirectImage_iso_homology`. Let `P` be a complex
over an open `U` of the base with `g^* P ≅ R f'_* g'^* ℱ` in the derived category for every base
change `f'` of `f` along a morphism `g` into `U`. Let `f' : X' ⟶ T'` be the base change of `f`
along `g : T' ⟶ T`, and `V` an open of `T'` which `g` maps into `U`. Then the restriction of
`R f'_* ℱ'` to `V` is isomorphic to the pullback of `P` to `V` in `D(𝒪_V)`. -/
theorem nonempty_restrict_derivedPushforward_iso {U : T.Opens}
    {P : CochainComplex U.toScheme.Modules ℤ}
    (hbc : ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T'),
      IsPullback g' f' f (g ≫ U.ι) →
        Nonempty (DerivedCategory.Q.obj (((Modules.pullback g).mapHomologicalComplex _).obj P) ≅
          (derivedPushforward f').obj
            ((DerivedCategory.singleFunctor _ 0).obj ((Modules.pullback g').obj ℱ))))
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (sq : IsPullback g' f' f g) (V : T'.Opens)
    (gV : V.toScheme ⟶ U.toScheme) (hgV : gV ≫ U.ι = V.ι ≫ g) :
    Nonempty ((restrictFunctor V.ι).mapDerivedCategory.obj ((derivedPushforward f').obj
        ((DerivedCategory.singleFunctor _ 0).obj ((Modules.pullback g').obj ℱ))) ≅
      DerivedCategory.Q.obj (((Modules.pullback gV).mapHomologicalComplex _).obj P)) := by
  have sq' : IsPullback ((f' ⁻¹ᵁ V).ι ≫ g') (f' ∣_ V) f (gV ≫ U.ι) := by
    rw [hgV]
    exact (isPullback_morphismRestrict f' V).flip.paste_horiz sq
  obtain ⟨e⟩ := hbc gV _ _ sq'
  exact ⟨restrictDerivedPushforwardIso ℱ g' f' V e⟩

/-- **`R f'_* ℱ'` is locally finite locally free in one degree over `U_{i,r}`.** Let `f' : X' ⟶ T'`
be the base change of `f` along `g : T' ⟶ T`, and `t'` a point of `T'` mapped into the rank-`r`
perfect locus `U_{i,r}`. Then `t'` has an open neighbourhood `V` over which `R f'_* ℱ'` is a finite
locally free module of rank `r` placed in degree `i`. -/
theorem exists_mem_isFiniteLocallyFreeInDegree_restrict (hℱ : ℱ.IsFlatOver f) {i r : ℕ}
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g) (t' : T')
    (ht' : g.base t' ∈ ℱ.perfectLocusOfRank f i r) :
    ∃ V : T'.Opens, t' ∈ V ∧ IsFiniteLocallyFreeInDegree
      (fun q ↦ ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)).restrict V.ι) i r := by
  obtain ⟨U, P, d, hsU, hP, hbc⟩ := exists_isFiniteFreeComplex_higherDirectImage f ℱ hℱ (g.base t')
  obtain ⟨UP, hUP⟩ := hP.exists_opens_range_subset_iff i r
  obtain ⟨gs, hgs⟩ := exists_comp_ι_eq_fromSpecResidueField hsU
  have hs : Set.range gs.base ⊆ UP :=
    (hUP gs).2 ((isFiniteLocallyFreeInDegree_homology_pullback_iff f ℱ hP hbc gs hgs i r).2 ht')
  obtain ⟨x⟩ : Nonempty (Spec (T.residueField (g.base t'))) := inferInstance
  have hx : U.ι.base (gs.base x) = g.base t' := by
    rw [← Scheme.Hom.comp_apply, hgs]
    exact (Scheme.range_fromSpecResidueField (g.base t')).subset ⟨x, rfl⟩
  let V := g ⁻¹ᵁ (U.ι ''ᵁ UP)
  have hV : t' ∈ V := ⟨gs.base x, hs ⟨x, rfl⟩, hx⟩
  have hgV : Set.range (V.ι ≫ g).base ⊆ Set.range U.ι.base := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, -, hu⟩ := w.2
    exact ⟨u, by simpa using hu⟩
  let gV := IsOpenImmersion.lift U.ι (V.ι ≫ g) hgV
  have hgV' : gV ≫ U.ι = V.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have hrange : Set.range gV.base ⊆ UP := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨u, hu, hu'⟩ := w.2
    have : U.ι.base (gV.base w) = U.ι.base u := by
      rw [← Scheme.Hom.comp_apply, hgV', Scheme.Hom.comp_apply]
      exact hu'.symm
    rwa [U.ι.isOpenEmbedding.injective this]
  have h := (hUP gV).1 hrange
  have e q := (nonempty_restrict_higherDirectImage_iso_homology f ℱ hbc g g' f' sq V gV hgV' q).some
  exact ⟨V, hV, fun q hq ↦ (h.isZero q hq).of_iso (e q),
    have := h.isFiniteLocallyFreeOfRank
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (e i).symm⟩

/-- **Vanishing off degree `i` after base change to the perfect locus.** Let `g : T' ⟶ T` have
image in the perfect locus `U_i`, and let `f' : X' ⟶ T'` and `g' : X' ⟶ X` be the base change of
`f` along `g`, in the cartesian square `sq`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
with `ℱ'` the pullback of `ℱ` to `X'`. Then the higher direct images `R^q f'_* ℱ'` vanish for
`q ≠ i`.

Together with
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_higherDirectImage_of_isPullback`
this is the concrete form of "`R f'_* ℱ'` is perfect of amplitude `[i, i]`", there being no
derived category of `X.Modules` available.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem isZero_higherDirectImage_of_isPullback (hℱ : ℱ.IsFlatOver f) {i : ℕ}
    {T' X' : Scheme.{u}} (g : T' ⟶ T) (g' : X' ⟶ X) (f' : X' ⟶ T')
    [HasInjectiveResolutions X'.Modules] (sq : IsPullback g' f' f g)
    (hg : Set.range g.base ⊆ ℱ.perfectLocus f i) {q : ℕ} (hq : q ≠ i) :
    IsZero ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ)) := by
  choose V hV h using fun t' ↦ exists_mem_isFiniteLocallyFreeInDegree_restrict f ℱ hℱ g g' f' sq
    t' (r := ℱ.hFiber f i (g.base t')) ⟨hg ⟨t', rfl⟩, rfl⟩
  exact isZero_of_iSup_eq_top _ V (eq_top_iff.2 fun t' _ ↦
    TopologicalSpace.Opens.mem_iSup.2 ⟨t', hV t'⟩) fun t' ↦ (h t').isZero q hq

/-- **The higher direct images vanish off degree `i` over the perfect locus.** Over an open
subscheme `U` of `T` contained in the rank-`r` perfect locus `U_{i,r}`, the higher direct images
`R^q f_* ℱ|_U` vanish for `q ≠ i`. This is the case of the inclusion of `U` in
`AlgebraicGeometry.Scheme.Modules.isZero_higherDirectImage_of_isPullback`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem isZero_higherDirectImage_restrict (hℱ : ℱ.IsFlatOver f) (i r : ℕ) (U : T.Opens)
    (hU : ↑U ⊆ {t : T | (∀ q, q ≠ i → ℱ.hFiber f q t = 0) ∧ ℱ.hFiber f i t = r})
    (q : ℕ) (hq : q ≠ i) :
    IsZero (((higherDirectImage f q).obj ℱ).restrict U.ι) := by
  have := isGrothendieckAbelian (f ⁻¹ᵁ U).toScheme
  have sq : IsPullback (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι := (isPullback_morphismRestrict f U).flip
  obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ U.ι _ _ sq q
  refine (isZero_higherDirectImage_of_isPullback f ℱ hℱ U.ι _ _ sq ?_ hq).of_iso e.symm
  rw [Scheme.Opens.range_ι]
  exact fun t ht ↦ (hU ht).1

end Coherence

end AlgebraicGeometry.Scheme.Modules
