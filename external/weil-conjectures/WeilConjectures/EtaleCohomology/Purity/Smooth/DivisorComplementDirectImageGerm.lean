/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DivisorComplementDirectImage
public import WeilConjectures.AlgebraicGeometry.Morphisms.RegularImmersionStalk
public import WeilConjectures.AlgebraicGeometry.ZeroLocusSubschemeRegular
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.OpenImmersion.ClosedRestriction

/-!
# Direct images from the complement of the zero locus of a function

Let `X` be smooth over an algebraically closed field `k`, `t` a function on an open `V` of `X`
and `x ∈ V` a point at which the germ of `t` lies in `𝔪ₓ \ 𝔪ₓ²`. Then near `x` the zero locus of
`t` is a regular divisor with regular local rings
(`AlgebraicGeometry.exists_isRegularImmersion_zeroLocusSubschemeι_of_germ`), and purity
(`AlgebraicGeometry.Etale.exists_hasDivisorComplementDirectImages_of_isRegularImmersion`) computes
the higher direct images of `ℤ/ℓ` along the inclusion of the complement `X_t`:

`R⁰j_* ℤ/ℓ ≅ ℤ/ℓ`, `R¹j_* ℤ/ℓ ≅ i_* ℤ/ℓ` and `R^q j_* ℤ/ℓ = 0` for `q ≥ 2`

on a neighbourhood `X₀` of `x`, for every open immersion `j` onto `X₀ ∩ X_t` and a closed
immersion `i` onto `X₀ - X_t` (blueprint `lemma-punctured-surface-punctured-curve--1`, the local
chart of an étale limit of smooth surfaces).

## Main statements

- `AlgebraicGeometry.Etale.exists_hasDivisorComplementDirectImages_of_germ`
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

/-- **The zero locus of a function with germ in `𝔪 \ 𝔪²` is a regular divisor nearby.** Let `X`
be smooth over a perfect field `k`, `t` a function on an open `V` of `X` and `x ∈ V` a point
at which the germ of `t` lies in `𝔪ₓ` but not in `𝔪ₓ²`. Then there is an open neighbourhood
`X₁ ⊆ V` of `x` on which the zero locus `V(t)` of `t` is a regular closed immersion of
codimension one with regular local rings. -/
theorem exists_isRegularImmersion_zeroLocusSubschemeι_of_germ {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [Smooth aX] (V : X.Opens)
    (t : Γ(X, V)) (x : X) (hx : x ∈ V)
    (ht : X.presheaf.germ V x hx t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (ht2 : X.presheaf.germ V x hx t ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2) :
    ∃ (X₁ : X.Opens) (hX₁ : X₁ ≤ V), x ∈ X₁ ∧
      IsRegularImmersion 1 (X₁.toScheme.zeroLocusSubschemeι
        {X₁.topIso.inv (X.presheaf.map (homOfLE hX₁).op t)}) ∧
      ∀ z, IsRegularLocalRing ((X₁.toScheme.zeroLocusSubscheme
        {X₁.topIso.inv (X.presheaf.map (homOfLE hX₁).op t)}).presheaf.stalk z) := by
  have := LocallyOfFiniteType.isLocallyNoetherian aX
  have := IsRegular.of_smooth aX
  obtain ⟨C, hxC, hC⟩ := X.exists_mem_isPreirreducible_of_isDomain_stalk (fun _ ↦ inferInstance) x
  let W := V ⊓ C
  have hWV : W ≤ V := inf_le_left
  have hxW : x ∈ W := ⟨hx, hxC⟩
  let tW := W.topIso.inv (X.presheaf.map (homOfLE hWV).op t)
  let iW := W.toScheme.zeroLocusSubschemeι {tW}
  let S := (iW ≫ W.ι ≫ aX).smoothLocus
  have hB : IsClosed (iW '' (S : Set _)ᶜ) :=
    iW.isClosedEmbedding.isClosedMap _ S.isOpen.isClosed_compl
  let X₁ : X.Opens := W.ι ''ᵁ ⟨_, hB.isOpen_compl⟩
  have hX₁W : X₁ ≤ W := W.ι_image_le _
  have hX₁ : X₁ ≤ V := hX₁W.trans hWV
  have hRx : IsRegularLocalRing (X.presheaf.stalk x ⧸ Ideal.span {X.presheaf.germ V x hx t}) := by
    have := Smooth.isRegularLocalRing_stalk aX x
    obtain ⟨_, h, -⟩ := IsRegularLocalRing.quotient_span_singleton ht ht2
    exact h
  have hxX₁ : x ∈ X₁ := by
    refine (W.mem_ι_image_iff (x := ⟨x, hxW⟩)).mpr ?_
    rintro ⟨z, hzS, hz⟩
    refine hzS ?_
    have := (W.isRegularLocalRing_stalk_zeroLocusSubscheme_iff hWV t z hx
      (congrArg Subtype.val hz)).mpr hRx
    exact Scheme.Hom.mem_smoothLocus_of_isRegularLocalRing_of_perfectField _
  set t₁ : Γ(X₁.toScheme, ⊤) := X₁.topIso.inv (X.presheaf.map (homOfLE hX₁).op t)
    with ht₁_def
  set i₁ := X₁.toScheme.zeroLocusSubschemeι {t₁}
  refine ⟨X₁, hX₁, hxX₁, ?_, fun z ↦ ?_⟩
  · have hirr : IrreducibleSpace X₁ := Subtype.irreducibleSpace
      ⟨⟨x, hxX₁⟩, hC.open_subset X₁.isOpen (hX₁W.trans inf_le_right)⟩
    have : IsReduced X := isReduced_of_isReduced_stalk X
    have : IsIntegral X₁.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
    have ht₁ : t₁ ≠ 0 := by
      intro h0
      apply ht2
      have h0' : X.presheaf.map (homOfLE hX₁).op t = 0 := by
        rw [← CommRingCat.hom_inv_apply X₁.topIso (X.presheaf.map (homOfLE hX₁).op t),
          ← ht₁_def, h0, map_zero]
      rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hX₁) x hxX₁, h0', map_zero]
      exact zero_mem _
    refine IsRegularImmersion.of_stalk 1 one_ne_zero _ fun z ↦
      ⟨[X₁.toScheme.presheaf.germ ⊤ (i₁ z) trivial t₁], rfl, ?_, ?_⟩
    · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
      exact (IsRegular.of_ne_zero ((map_ne_zero_iff _
        (germ_injective_of_isIntegral X₁.toScheme (U := ⊤) _ trivial)).mpr ht₁)).left
    · rw [Ideal.ofList_singleton, Scheme.ker_stalkMap_zeroLocusSubschemeι_singleton]
  · have hs : (X.homOfLE hX₁W).appTop '' {tW} = {t₁} := by
      rw [Set.image_singleton, Scheme.homOfLE_appTop_topIso_inv,
        ← ConcreteCategory.comp_apply (X.presheaf.map _) (X.presheaf.map _), ← Functor.map_comp]
      rfl
    let g := (X.homOfLE hX₁W).zeroLocusSubschemeMap {tW} _ hs
    have hg : iW (g z) = X.homOfLE hX₁W (i₁ z) := by
      rw [← Scheme.Hom.comp_apply,
        Scheme.Hom.zeroLocusSubschemeMap_zeroLocusSubschemeι (X.homOfLE hX₁W) {tW} _ hs,
        Scheme.Hom.comp_apply]
    have hgS : g z ∈ S := by
      by_contra h
      have h' : X.homOfLE hX₁W (i₁ z) ∈ (iW '' (S : Set _)ᶜ)ᶜ :=
        (W.mem_ι_image_iff (V := ⟨_, hB.isOpen_compl⟩)).mp (by simp)
      exact h' ⟨g z, h, hg⟩
    have hreg := Scheme.Hom.isRegularLocalRing_stalk_of_mem_smoothLocus _ hgS
    have hp := hX₁ (i₁ z).2
    rw [W.isRegularLocalRing_stalk_zeroLocusSubscheme_iff hWV t (g z) hp
      (by rw [hg, Scheme.homOfLE_apply])] at hreg
    exact (X₁.isRegularLocalRing_stalk_zeroLocusSubscheme_iff hX₁ t z hp rfl).mpr hreg

namespace Etale

/-- **Direct images from the complement of the zero locus of a function** (blueprint
`lemma-punctured-surface-punctured-curve--1`). Let `X` be smooth over an algebraically closed field
`k`, `t` a function on an open `V` of `X` and `x ∈ V` a point at which the germ of `t` lies in
`𝔪ₓ \ 𝔪ₓ²`. There are an open neighbourhood `X₀ ⊆ V` of `x` and a closed immersion `i₀` onto
`X₀ - X_t` such that every open immersion `j₀` onto `X₀ ∩ X_t` has the higher direct images of
the complement of the divisor `i₀`:

`R⁰j₀_* ℤ/ℓ ≅ ℤ/ℓ`, `R¹j₀_* ℤ/ℓ ≅ i₀_* ℤ/ℓ` and `R^q j₀_* ℤ/ℓ = 0` for `q ≥ 2`. -/
theorem exists_hasDivisorComplementDirectImages_of_germ {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [Smooth aX] (V : X.Opens) (t : Γ(X, V)) (x : X)
    (hx : x ∈ V)
    (ht : X.presheaf.germ V x hx t ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (ht2 : X.presheaf.germ V x hx t ∉ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ 2)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0) :
    ∃ (X₀ : X.Opens), X₀ ≤ V ∧ x ∈ X₀ ∧ ∃ (D₀ : Scheme.{u}) (i₀ : D₀ ⟶ X₀)
      (_ : IsClosedImmersion i₀), Set.range (i₀ ≫ X₀.ι) = (X₀ : Set X) \ X.basicOpen t ∧
      ∀ (U₀ : Scheme.{u}) (j₀ : U₀ ⟶ X₀) [IsOpenImmersion j₀],
        Set.range (j₀ ≫ X₀.ι) = (X₀ : Set X) ∩ X.basicOpen t →
        HasDivisorComplementDirectImages ℓ j₀ i₀ := by
  obtain ⟨X₁, hX₁, hxX₁, hreg, hZ⟩ :=
    exists_isRegularImmersion_zeroLocusSubschemeι_of_germ aX V t x hx ht ht2
  let t₁ : Γ(X₁.toScheme, ⊤) := X₁.topIso.inv (X.presheaf.map (homOfLE hX₁).op t)
  let i := X₁.toScheme.zeroLocusSubschemeι {t₁}
  let j := (X₁.toScheme.basicOpen t₁).ι
  have hj : Set.range j = (Set.range i)ᶜ := by
    rw [Scheme.range_zeroLocusSubschemeι_singleton, compl_compl]
  obtain ⟨z, hz⟩ := X₁.exists_zeroLocusSubschemeι_eq _ ⟨x, hxX₁⟩
    (by rwa [TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hX₁)])
  obtain ⟨W₀, hzW₀, hD⟩ := exists_hasDivisorComplementDirectImages_of_isRegularImmersion
    (X₁.ι ≫ aX) i hZ j hj ℓ hℓ z
  let X₀ : X.Opens := X₁.ι ''ᵁ W₀
  have hX₀X₁ : X₀ ≤ X₁ := X₁.ι_image_le W₀
  have hrange : Set.range X₀.ι = Set.range (W₀.ι ≫ X₁.ι) := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    rfl
  let φ := IsOpenImmersion.isoOfRangeEq X₀.ι (W₀.ι ≫ X₁.ι) hrange
  have hφ : φ.hom ≫ W₀.ι ≫ X₁.ι = X₀.ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hB : X₁.ι '' (X₁.toScheme.basicOpen t₁ : Set X₁) = (X₁ : Set X) ∩ X.basicOpen t := by
    rw [← Scheme.Hom.coe_image, Scheme.Opens.ι_image_basicOpen_topIso_inv, Scheme.basicOpen_res]
    rfl
  have hW₀ : X₁.ι '' (W₀ : Set X₁) = X₀ := rfl
  refine ⟨X₀, hX₀X₁.trans hX₁, X₁.mem_ι_image_iff.mpr (hz ▸ hzW₀), _,
    pullback.snd (pullback.snd i W₀.ι) φ.hom, inferInstance, ?_, fun U₀ j₀ _ hj₀ ↦ ?_⟩
  · have h : pullback.snd (pullback.snd i W₀.ι) φ.hom ≫ X₀.ι =
        (pullback.snd (pullback.snd i W₀.ι) φ.hom ≫ φ.hom) ≫ W₀.ι ≫ X₁.ι := by
      rw [Category.assoc, hφ]
    rw [h, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_snd_comp,
      Set.range_eq_univ.mpr φ.hom.surjective, Set.inter_univ, ← Set.range_comp,
      ← TopCat.coe_comp, ← Scheme.Hom.comp_base, ← Category.assoc,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Pullback.range_snd_comp,
      Scheme.Opens.range_ι, Set.image_inter X₁.ι.isOpenEmbedding.injective, hW₀,
      Scheme.range_zeroLocusSubschemeι_singleton, Scheme.Opens.range_ι,
      Set.image_compl_eq_range_sdiff_image X₁.ι.isOpenEmbedding.injective,
      Scheme.Opens.range_ι, hB]
    ext y
    have hy : y ∈ X₀ → y ∈ X₁ := fun h ↦ hX₀X₁ h
    simp only [Set.mem_inter_iff, Set.mem_sdiff, SetLike.mem_coe] at hy ⊢
    tauto
  · have hr : Set.range (j₀ ≫ X₀.ι) = Set.range (pullback.snd j W₀.ι ≫ W₀.ι ≫ X₁.ι) := by
      rw [hj₀, ← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Scheme.Pullback.range_snd_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι,
        Set.image_inter X₁.ι.isOpenEmbedding.injective, hW₀, hB]
      ext y
      have hy : y ∈ X₀ → y ∈ X₁ := fun h ↦ hX₀X₁ h
      simp only [Set.mem_inter_iff, SetLike.mem_coe] at hy ⊢
      tauto
    let e := IsOpenImmersion.isoOfRangeEq (j₀ ≫ X₀.ι) (pullback.snd j W₀.ι ≫ W₀.ι ≫ X₁.ι) hr
    have he : e.hom ≫ pullback.snd j W₀.ι = j₀ ≫ φ.hom := by
      rw [← cancel_mono (W₀.ι ≫ X₁.ι), Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac,
        Category.assoc, hφ]
    have sq : IsPullback e.hom j₀ (pullback.snd j W₀.ι) φ.hom := IsPullback.of_horiz_isIso ⟨he⟩
    exact hD.of_isPullback φ.hom sq fun q ↦ isIso_baseChangeHomologyMap_of_etale _ sq q _

end Etale

end AlgebraicGeometry
