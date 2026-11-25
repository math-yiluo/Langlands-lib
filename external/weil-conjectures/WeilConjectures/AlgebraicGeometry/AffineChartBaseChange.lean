/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Base change of closed and open immersions to an affine probe through a chart

Let `W` be an affine open of a scheme `Z`, with ring `R = Γ(Z, W)`, and let `φ : R ⟶ S` be a ring
map, so that `Spec.map φ ≫ W.2.fromSpec : Spec S ⟶ Z` is an affine probe through the chart `W`.

- The base change of a closed immersion `i : X ⟶ Z` with ideal `I` along the probe is
  `Spec (S ⧸ I(W) S) ⟶ Spec S`
  (`AlgebraicGeometry.IsClosedImmersion.isPullback_specMap_fromSpec`).
- The base change of an open immersion `j : U ⟶ Z` whose image meets `W` in the basic open of
  `t ∈ R` is `Spec S_{φ t} ⟶ Spec S`
  (`AlgebraicGeometry.IsOpenImmersion.isPullback_specMap_away_fromSpec`).
- The intersection of two closed subschemes is cut out by the sum of their ideals
  (`AlgebraicGeometry.Scheme.Hom.ker_pullback_fst_comp`).

These are used to compute the strict localization of a transverse corner and its punctured
divisors (blueprint `lemma-punctured-surface-punctured-curve--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Z : Scheme.{u}}

/-- **Base change of a closed immersion to an affine probe.** For a closed immersion
`i : X ⟶ Z`, an affine open `W` of `Z` and `φ : Γ(Z, W) ⟶ S`, the base change of `i` along
`Spec.map φ ≫ W.2.fromSpec` is `Spec (S ⧸ I(W) S) ⟶ Spec S`, where `I = ker i`. -/
lemma IsClosedImmersion.isPullback_specMap_fromSpec (i : X ⟶ Z) [IsClosedImmersion i]
    (W : Z.affineOpens) {S : CommRingCat.{u}} (φ : Γ(Z, W.1) ⟶ S) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((i.ker.ideal W).map φ.hom) φ.hom
        Ideal.le_comap_map)) ≫ i.ker.subschemeCover.f W ≫ inv i.toImage)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((i.ker.ideal W).map φ.hom))))
      i (Spec.map φ ≫ W.2.fromSpec) := by
  have h := i.ker.isPullback_subschemeι_specMap_fromSpec W φ
  have e : inv i.toImage ≫ i = i.imageι := by
    rw [IsIso.inv_comp_eq, Scheme.Hom.toImage_imageι]
  refine IsPullback.of_iso h (Iso.refl _) (asIso i.toImage).symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp [e]) (by simp)

/-- **Base change of an open immersion to an affine probe.** Let `j : U ⟶ Z` be an open
immersion whose image meets the affine open `W` in the basic open of `t ∈ Γ(Z, W)`. For
`φ : Γ(Z, W) ⟶ S`, the base change of `j` along `Spec.map φ ≫ W.2.fromSpec` is
`Spec S_{φ t} ⟶ Spec S`. -/
lemma IsOpenImmersion.isPullback_specMap_away_fromSpec {U : Scheme.{u}} (j : U ⟶ Z)
    [IsOpenImmersion j] (W : Z.affineOpens) (t : Γ(Z, W.1))
    (hj : Set.range j ∩ (W : Set Z) = Z.basicOpen t) {S : CommRingCat.{u}}
    (φ : Γ(Z, W.1) ⟶ S) :
    ∃ g : Spec (.of (Localization.Away (φ.hom t))) ⟶ U,
      IsPullback g (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (φ.hom t)))))
        j (Spec.map φ ≫ W.2.fromSpec) := by
  set f := Spec.map φ ≫ W.2.fromSpec
  set ι := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (φ.hom t))))
  have H' : f ⁻¹ᵁ j.opensRange = ι.opensRange := by
    ext x
    have hx : f x ∈ (W : Set Z) := by
      rw [← W.2.range_fromSpec]
      exact ⟨_, rfl⟩
    rw [SetLike.mem_coe, Scheme.Hom.mem_preimage]
    simp only [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]
    rw [← and_iff_left (a := f x ∈ Set.range j) hx, ← Set.mem_inter_iff, hj,
      Scheme.Hom.comp_apply, SetLike.mem_coe, ← Scheme.Hom.mem_preimage,
      W.2.fromSpec_preimage_basicOpen]
    exact (Set.ext_iff.1 (PrimeSpectrum.localization_away_comap_range
      (Localization.Away (φ.hom t)) (φ.hom t)) _).symm
  have hrange : Set.range (ι ≫ f) ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    have : ι x ∈ ι.opensRange := ⟨x, rfl⟩
    rw [← H'] at this
    exact this
  refine ⟨IsOpenImmersion.lift j (ι ≫ f) hrange, IsOpenImmersion.isPullback _ _ _ _ ?_ H'⟩
  exact (IsOpenImmersion.lift_fac j (ι ≫ f) hrange).symm

/-- **The intersection of two closed subschemes.** The kernel of the closed immersion
`X₁ ×_Z X₂ ⟶ Z` of the intersection of two closed subschemes is the sum of their ideals. -/
lemma Scheme.Hom.ker_pullback_fst_comp {X₁ X₂ : Scheme.{u}} (i₁ : X₁ ⟶ Z) (i₂ : X₂ ⟶ Z)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] :
    (pullback.fst i₁ i₂ ≫ i₁).ker = i₁.ker ⊔ i₂.ker := by
  refine le_antisymm ?_ (sup_le (Scheme.Hom.le_ker_comp _ _) ?_)
  · set I := i₁.ker ⊔ i₂.ker
    have h₁ : i₁.ker ≤ I.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact le_sup_left
    have h₂ : i₂.ker ≤ I.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact le_sup_right
    let m : I.subscheme ⟶ pullback i₁ i₂ :=
      pullback.lift (IsClosedImmersion.lift i₁ I.subschemeι h₁)
        (IsClosedImmersion.lift i₂ I.subschemeι h₂) (by simp)
    have hm : m ≫ pullback.fst i₁ i₂ ≫ i₁ = I.subschemeι := by simp [m]
    calc (pullback.fst i₁ i₂ ≫ i₁).ker ≤ (m ≫ pullback.fst i₁ i₂ ≫ i₁).ker :=
          Scheme.Hom.le_ker_comp _ _
      _ = I := by rw [hm, Scheme.IdealSheafData.ker_subschemeι]
  · rw [pullback.condition]
    exact Scheme.Hom.le_ker_comp _ _

/-- The image of a closed immersion meets an affine open `W` in the zero locus of its ideal
on `W`. -/
lemma IsClosedImmersion.mem_range_iff_mem_zeroLocus (i : X ⟶ Z) [IsClosedImmersion i]
    (W : Z.affineOpens) {x : Z} (hx : x ∈ W.1) :
    x ∈ Set.range i ↔ x ∈ Z.zeroLocus (U := W.1) (i.ker.ideal W) := by
  rw [← Scheme.IdealSheafData.mem_support_iff_of_mem hx]
  have h : Set.range i.base = Set.range i.imageι.base := by
    conv_lhs => rw [← i.toImage_imageι]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      (ConcreteCategory.bijective_of_isIso i.toImage.base).2.range_eq, Set.image_univ]
  rw [h]
  exact (congrArg (x ∈ ·) (Scheme.IdealSheafData.range_subschemeι _)).to_iff

/-- **Local rings of a closed subscheme through an affine chart.** Let `i : X ⟶ Z` be a closed
immersion, `W` an affine open of `Z` and `y` a prime of `Γ(Z, W)` whose point is `i x`. Then the
local ring of `X` at `x` is the quotient of the localization `Γ(Z, W)_y` by the ideal of `i` on
`W`. -/
lemma IsClosedImmersion.nonempty_ringEquiv_stalk (i : X ⟶ Z) [IsClosedImmersion i]
    (W : Z.affineOpens) (y : PrimeSpectrum Γ(Z, W.1)) (x : X) (hy : W.2.fromSpec y = i x) :
    Nonempty (Localization.AtPrime y.asIdeal ⧸ (i.ker.ideal W).map
      (algebraMap Γ(Z, W.1) (Localization.AtPrime y.asIdeal)) ≃+* X.presheaf.stalk x) := by
  have hxW : i x ∈ W.1 := by
    have h := Set.mem_range_self (f := W.2.fromSpec.base) y
    rw [W.2.range_fromSpec, hy] at h
    exact h
  obtain rfl : y = W.2.primeIdealOf ⟨i x, hxW⟩ :=
    W.2.fromSpec.isOpenEmbedding.injective (hy.trans (W.2.fromSpec_primeIdealOf ⟨i x, hxW⟩).symm)
  let := Z.presheaf.algebra_section_stalk ⟨i x, hxW⟩
  have := W.2.isLocalization_stalk ⟨i x, hxW⟩
  let e₁ := IsLocalization.algEquiv (W.2.primeIdealOf ⟨i x, hxW⟩).asIdeal.primeCompl
    (Localization.AtPrime (W.2.primeIdealOf ⟨i x, hxW⟩).asIdeal) (Z.presheaf.stalk (i x))
  have hI : ((i.ker.ideal W).map (algebraMap Γ(Z, W.1)
      (Localization.AtPrime (W.2.primeIdealOf ⟨i x, hxW⟩).asIdeal))).map e₁.toRingEquiv =
      RingHom.ker (i.stalkMap x).hom := by
    rw [i.ker_stalkMap W x hxW, ← Ideal.map_coe, Ideal.map_map]
    congr 1
    ext r
    exact e₁.commutes r
  exact ⟨(Ideal.quotientEquiv _ _ e₁.toRingEquiv hI.symm).trans
    (RingHom.quotientKerEquivOfSurjective (i.stalkMap_surjective x))⟩

/-- The local rings of a scheme with at most one point have dimension zero. -/
lemma Scheme.krullDimLE_zero_stalk_of_subsingleton [Subsingleton X] (x : X) :
    Ring.KrullDimLE 0 (X.presheaf.stalk x) :=
  krullDimLE_of_coheight_le (Order.coheight_eq_zero.2 fun _ _ ↦
    (Subsingleton.elim _ _).le).le

end AlgebraicGeometry

namespace CategoryTheory

variable {C : Type*} [Category C] [HasPullbacks C]

/-- **Computing an iterated pullback from models.** Let `i : X ⟶ Z`, `j : U ⟶ Z` and
`f : S ⟶ Z`, with models `XS` of `X ×_Z S` and `US` of `U ×_Z S`, and a model `P'` of
`XS ×_S US`. Then `P'` is a model of `(X ×_Z U) ×_U (U ×_Z S)`, compatibly with the projection
to `US ≅ U ×_Z S`. -/
lemma IsPullback.pullback_snd_pullback_fst {X Z U S XS US P' : C} {i : X ⟶ Z} {j : U ⟶ Z}
    {f : S ⟶ Z} {a : XS ⟶ X} {b : XS ⟶ S} {c : US ⟶ U} {d : US ⟶ S}
    (hX : IsPullback a b i f) (hU : IsPullback c d j f) {e₁ : P' ⟶ XS} {e₂ : P' ⟶ US}
    (hP : IsPullback e₁ e₂ b d) :
    IsPullback (pullback.lift (e₁ ≫ a) (e₂ ≫ c) (by
        rw [Category.assoc, Category.assoc, hX.w, hU.w, reassoc_of% hP.w]))
      (e₂ ≫ hU.isoPullback.hom) (pullback.snd i j) (pullback.fst j f) := by
  have hP' : IsPullback e₁ (e₂ ≫ hU.isoPullback.hom) b (pullback.snd j f) :=
    IsPullback.of_iso hP (Iso.refl _) (Iso.refl _) hU.isoPullback (Iso.refl _) (by simp)
      (by simp) (by simp) (by simp)
  have big := hP'.paste_horiz hX
  rw [← pullback.condition] at big
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback i j)
  simpa using big

end CategoryTheory
