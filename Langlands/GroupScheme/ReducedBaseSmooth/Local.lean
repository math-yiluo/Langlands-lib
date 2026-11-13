import Langlands.GroupScheme.ReducedBaseSmooth.FibreTransfer

/-! # The section lies in the smooth locus, given a local closed embedding into a smooth scheme -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.ReducedBaseSmooth

/-- **Local criterion.** Let `q : Y → S` have a section `e` over a reduced base, with residue
fibres over an open `U ∋ s` smooth of relative dimension `n`. Suppose that near `s` and `e s`
the morphism `q` is a closed subscheme of a scheme smooth of relative dimension `n`: open
immersions `ιV : V0 → S` and `ιY : Y0 → Y` hitting `s` and `e s`, a morphism `g : Y0 → V0`
compatible with `q`, and a factorisation `g = i0 ≫ p0` through a closed immersion `i0` into
`p0 : Z0 → V0`, smooth of relative dimension `n`, quasi-compact and quasi-separated. Then
`e s` lies in the smooth locus of `q`. -/
theorem mem_smoothLocus_of_closedImmersion_chart {S Y : Scheme.{u}} [IsReduced S] (q : Y ⟶ S)
    [LocallyOfFinitePresentation q] (e : S ⟶ Y) (he : e ≫ q = 𝟙 S) (n : ℕ) (U : S.Opens)
    (hU : ∀ t ∈ U, SmoothOfRelativeDimension n (q.fiberToSpecResidueField t))
    {V0 Y0 Z0 : Scheme.{u}} (ιV : V0 ⟶ S) [IsOpenImmersion ιV] (ιY : Y0 ⟶ Y)
    [IsOpenImmersion ιY] (g : Y0 ⟶ V0) (hg : g ≫ ιV = ιY ≫ q) (p0 : Z0 ⟶ V0)
    [SmoothOfRelativeDimension n p0] [QuasiCompact p0] [QuasiSeparated p0] (i0 : Y0 ⟶ Z0)
    [IsClosedImmersion i0] (hi0 : i0 ≫ p0 = g) (s : S) (hs : s ∈ U)
    (hsV : s ∈ Set.range ιV) (hsY : e s ∈ Set.range ιY) :
    e s ∈ q.smoothLocus := by
  -- The open neighbourhood of `s` on which everything is defined.
  let V' : S.Opens := ιV.opensRange ⊓ e ⁻¹ᵁ ιY.opensRange ⊓ U
  have hsV' : s ∈ V' := ⟨⟨hsV, hsY⟩, hs⟩
  have hV'V : Set.range V'.ι ⊆ Set.range ιV := by
    rw [Scheme.Opens.range_ι]; exact fun x hx => hx.1.1
  have hV'Y : Set.range (V'.ι ≫ e) ⊆ Set.range ιY := by
    rintro _ ⟨x, rfl⟩
    exact x.2.1.2
  let a : (V' : Scheme.{u}) ⟶ V0 := IsOpenImmersion.lift ιV V'.ι hV'V
  have ha : a ≫ ιV = V'.ι := IsOpenImmersion.lift_fac _ _ _
  let eT : (V' : Scheme.{u}) ⟶ Y0 := IsOpenImmersion.lift ιY (V'.ι ≫ e) hV'Y
  have heT : eT ≫ ιY = V'.ι ≫ e := IsOpenImmersion.lift_fac _ _ _
  have heTg : eT ≫ g = a := by
    rw [← cancel_mono ιV, Category.assoc, hg, ← Category.assoc, heT, Category.assoc, he,
      Category.comp_id, ha]
  -- Base change to `V'`.
  let p : pullback p0 a ⟶ (V' : Scheme.{u}) := pullback.snd p0 a
  let i : pullback g a ⟶ pullback p0 a :=
    pullback.map g a p0 a i0 (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hi0]) (by simp)
  have hip : i ≫ p = pullback.snd g a := by
    simp [i, p]
  have : IsClosedImmersion i :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance
      hi0.symm (by simp)
  let eY : (V' : Scheme.{u}) ⟶ pullback g a := pullback.lift eT (𝟙 _) (by simp [heTg])
  have heY : eY ≫ i ≫ p = 𝟙 _ := by
    rw [hip]; simp [eY]
  have hfib : ∀ t : (V' : Scheme.{u}),
      SmoothOfRelativeDimension n ((i ≫ p).fiberToSpecResidueField t) := by
    intro t
    rw [hip]
    apply smoothOfRelativeDimension_fiber_of_isPullback (IsPullback.of_hasPullback g a) t n
    have h1 : SmoothOfRelativeDimension n ((ιY ≫ q).fiberToSpecResidueField (V'.ι t)) :=
      smoothOfRelativeDimension_fiber_comp_of_isOpenImmersion ιY q _ n (hU _ t.2.2)
    rw [← hg, ← ha, Scheme.Hom.comp_apply] at h1
    exact smoothOfRelativeDimension_fiber_of_isPullback
      (IsPullback.of_horiz_isIso_mono (fst := 𝟙 Y0) (snd := g) (f := g ≫ ιV) (g := ιV)
        ⟨by simp⟩) (a t) n h1
  have : SmoothOfRelativeDimension n p :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ inferInstance
  have : QuasiCompact p := MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance
  have : QuasiSeparated p :=
    MorphismProperty.pullback_snd (P := @QuasiSeparated) _ _ inferInstance
  obtain ⟨W, hW, hWsm⟩ := exists_smooth_open_of_closedImmersion p n i eY heY hfib
  -- Transport smoothness back to `Y`.
  let ψ : (W : Scheme.{u}) ⟶ Y := W.ι ≫ pullback.fst g a ≫ ιY
  have hψ : ψ ≫ q = (W.ι ≫ i ≫ p) ≫ V'.ι := by
    simp only [ψ, Category.assoc, ← hg, hip]
    rw [pullback.condition_assoc, ha]
  have : Smooth (ψ ≫ q) := by rw [hψ]; infer_instance
  have hψtop : ψ ⁻¹ᵁ q.smoothLocus = ⊤ := by
    rw [Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
  let t0 : (V' : Scheme.{u}) := ⟨s, hsV'⟩
  have hw : eY t0 ∈ W := hW ⟨t0, rfl⟩
  have hmem : ψ ⟨eY t0, hw⟩ ∈ q.smoothLocus := by
    change (⟨eY t0, hw⟩ : W) ∈ ψ ⁻¹ᵁ q.smoothLocus
    rw [hψtop]; trivial
  have hψe : ψ ⟨eY t0, hw⟩ = e s := by
    change ιY (pullback.fst g a (W.ι ⟨eY t0, hw⟩)) = e s
    rw [Scheme.Opens.ι_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      pullback.lift_fst_assoc, heT, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  rwa [hψe] at hmem

end Langlands.GroupScheme.ReducedBaseSmooth
