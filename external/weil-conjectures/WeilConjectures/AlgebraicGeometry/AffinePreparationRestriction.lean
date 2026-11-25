/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-! # Affine restriction of a universally homeomorphic preparation

Source: Stacks Project, Tag 0559, second proof, generic-flat shrinking;
Tag 01IT for the affine-open basis.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Restrict an existing reduced affine preparation to an open where its family is flat
and locally finitely presented, retaining an affine open of the original base.

Source: Stacks Project, Tag 0559, second proof, generic-flat shrinking;
Tag 01IT for the affine-open basis.
Proof: q is a homeomorphism, so q(W) is open in V. Its image in T is open and contains
 η. Choose an affine open U about η contained in this image. Its inverse image S' in
 S is affine because q is an affine morphism (it is integral) and U is affine; it is
 integral because it is a nonempty open of the integral scheme S. Restrict Z to the
 inverse image of S', obtaining Z'. It is reduced as an open of Z and affine because
 the morphism from Z to S is affine (both schemes are affine). The restriction q'
 is the base change of q and is universally homeomorphic. Pullback pasting identifies
 X ×_T S' with the restriction of X ×_T S. Under this identification the restriction
 h' is a base change of h and is universally homeomorphic. Finally S' lies in W,
 so the restricted composite is a further restriction of the given flat, locally
 finitely presented family over W. Both properties are local on the target and are
 preserved by restriction. This construction also works for an empty Z.

(blueprint: lem-sbc-affine-preparation-restriction) -/
theorem exists_affine_preparation_restriction
    {X T S Z : Scheme.{u}} (f : X ⟶ T)
    (V : T.Opens) (q : S ⟶ V.toScheme)
    (h : Z ⟶ pullback f (q ≫ V.ι))
    [IsAffine S] [IsIntegral S] [IsAffine Z] [IsReduced Z]
    [IsUniversalHomeomorphism q] [IsUniversalHomeomorphism h]
    (W : S.Opens) (hflat : Flat ((h ≫ pullback.snd f (q ≫ V.ι)) ∣_ W))
    (hfp : LocallyOfFinitePresentation ((h ≫ pullback.snd f (q ≫ V.ι)) ∣_ W))
    (η₀ : S) (hη₀W : η₀ ∈ W) (η : T) (he : (q ≫ V.ι) η₀ = η) :
    ∃ (U : T.Opens), η ∈ U ∧ IsAffineOpen U ∧
      ∃ (S' Z' : Scheme.{u}) (q' : S' ⟶ U.toScheme)
        (h' : Z' ⟶ pullback f (q' ≫ U.ι)),
        IsAffine S' ∧ IsIntegral S' ∧ IsAffine Z' ∧ IsReduced Z' ∧
        IsUniversalHomeomorphism q' ∧ IsUniversalHomeomorphism h' ∧
        Flat (h' ≫ pullback.snd f (q' ≫ U.ι)) ∧
        LocallyOfFinitePresentation (h' ≫ pullback.snd f (q' ≫ U.ι)) := by
  let g := h ≫ pullback.snd f (q ≫ V.ι)
  let qT := q ≫ V.ι
  have hO : IsOpen (qT '' (W : Set S)) := by
    have hqTf : (qT : S → T) = V.ι ∘ q := by
      funext s
      exact Scheme.Hom.comp_apply q V.ι s
    rw [hqTf]
    simpa only [Function.comp_def, Set.image_image] using
      V.ι.isOpenEmbedding.isOpenMap _ (q.isHomeomorph.isOpenMap _ W.isOpen)
  have hηO : η ∈ qT '' (W : Set S) := ⟨η₀, hη₀W, he⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, hUO⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open hηO hO
  let U : T.Opens := U
  have hU : IsAffineOpen U := hU
  have hUV : U ≤ V := by
    intro t ht
    obtain ⟨s, _, rfl⟩ := hUO ht
    exact (q s).property
  have hUr : Set.range U.ι ⊆ Set.range V.ι := by
    simpa only [Scheme.Opens.range_ι] using (show (U : Set T) ⊆ V from hUV)
  let k : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι U.ι hUr
  have hk : k ≫ V.ι = U.ι := IsOpenImmersion.lift_fac V.ι U.ι hUr
  let A := qT ⁻¹ᵁ U
  let p := A.ι
  let q' := qT ∣_ U
  have hpq : p ≫ q = q' ≫ k := by
    apply (cancel_mono V.ι).mp
    simp only [Category.assoc]
    rw [hk]
    exact (morphismRestrict_ι qT U).symm
  have hpre : q ⁻¹ᵁ k.opensRange = A := by
    ext s
    constructor
    · rintro ⟨u, hu⟩
      change qT s ∈ U
      have heq := congrArg (fun a : U.toScheme ⟶ T ↦ a u) hk
      have heqs : qT s = U.ι u := by
        change V.ι (q s) = U.ι u
        rw [← hu]
        exact heq
      change qT s ∈ U
      rw [heqs]
      exact u.property
    · intro hs
      refine ⟨⟨qT s, hs⟩, ?_⟩
      apply V.ι.isOpenEmbedding.injective
      have heq := congrArg (fun a : U.toScheme ⟶ T ↦ a ⟨qT s, hs⟩) hk
      exact heq
  have Hq := IsOpenImmersion.isPullback q' p k q hpq
    (by simpa only [p, Scheme.Opens.opensRange_ι] using hpre)
  let : IsUniversalHomeomorphism q' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback Hq.flip inferInstance
  have hAa : IsAffineOpen A :=
    (hU.preimage_of_isOpenImmersion V.ι (by simpa using hUV)).preimage q
  let : IsAffine A.toScheme := hAa
  have hη₀A : η₀ ∈ A := by change qT η₀ ∈ U; rwa [he]
  let : Nonempty A.toScheme := ⟨⟨η₀, hη₀A⟩⟩
  let : IsIntegral A.toScheme := isIntegral_of_isOpenImmersion p
  have hAW : A ≤ W := by
    intro s hs
    obtain ⟨t, ht, heq⟩ := hUO hs
    have hts : t = s :=
      q.isHomeomorph.injective (V.ι.isOpenEmbedding.injective heq)
    rwa [hts] at ht
  let C := g ⁻¹ᵁ A
  let : IsAffine C.toScheme := (hAa.preimage g)
  let : IsReduced C.toScheme := isReduced_of_isOpenImmersion C.ι
  let g' := g ∣_ A
  have hflat' : Flat g' := by
    have h := IsZariskiLocalAtTarget.restrict hflat (W.ι ⁻¹ᵁ A)
    have h' := (MorphismProperty.arrow_mk_iso_iff @Flat
      (morphismRestrictRestrict g W (W.ι ⁻¹ᵁ A))).mp h
    have heq : W.ι ''ᵁ W.ι ⁻¹ᵁ A = A := by
      ext s
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ht
      · intro hs; exact ⟨⟨s, hAW hs⟩, hs, rfl⟩
    rwa [heq] at h'
  have hfp' : LocallyOfFinitePresentation g' := by
    have h := IsZariskiLocalAtTarget.restrict hfp (W.ι ⁻¹ᵁ A)
    have h' := (MorphismProperty.arrow_mk_iso_iff @LocallyOfFinitePresentation
      (morphismRestrictRestrict g W (W.ι ⁻¹ᵁ A))).mp h
    have heq : W.ι ''ᵁ W.ι ⁻¹ᵁ A = A := by
      ext s
      constructor
      · rintro ⟨t, ht, rfl⟩; exact ht
      · intro hs; exact ⟨⟨s, hAW hs⟩, hs, rfl⟩
    rwa [heq] at h'
  let e : pullback (pullback.snd f qT) p ≅ pullback f (q' ≫ U.ι) :=
    pullbackLeftPullbackSndIso f qT p ≪≫
      pullback.congrHom rfl (morphismRestrict_ι qT U).symm
  let j := e.inv ≫ pullback.fst (pullback.snd f qT) p
  have hjfst : j ≫ pullback.fst f qT = pullback.fst f (q' ≫ U.ι) := by
    simp [j, e, Category.assoc, pullback.map, p, q', A]
  have hjsnd : j ≫ pullback.snd f qT = pullback.snd f (q' ≫ U.ι) ≫ p := by
    simp [j, e, Category.assoc, pullback.map, p, q', A]
  have hjrange : j.opensRange = pullback.snd f qT ⁻¹ᵁ A := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Hom.opensRange_pullbackFst,
      Scheme.Opens.opensRange_ι]
  let h' : C.toScheme ⟶ pullback f (q' ≫ U.ι) :=
    pullback.lift (C.ι ≫ h ≫ pullback.fst f qT) g' (by
      calc
        (C.ι ≫ h ≫ pullback.fst f qT) ≫ f = C.ι ≫ g ≫ qT := by
          simp only [g, qT, Category.assoc, pullback.condition]
        _ = g' ≫ p ≫ qT := by
          simpa only [Category.assoc] using
            congrArg (fun a ↦ a ≫ qT) (morphismRestrict_ι g A).symm
        _ = g' ≫ (q' ≫ U.ι) := by rw [← morphismRestrict_ι qT U])
  have hhj : C.ι ≫ h = h' ≫ j := by
    apply pullback.hom_ext
    · change C.ι ≫ h ≫ pullback.fst f qT = h' ≫ j ≫ pullback.fst f qT
      rw [hjfst]
      dsimp only [h']
      rw [pullback.lift_fst]
    · change C.ι ≫ h ≫ pullback.snd f qT = h' ≫ j ≫ pullback.snd f qT
      rw [hjsnd]
      dsimp only [h']
      rw [pullback.lift_snd_assoc]
      exact (morphismRestrict_ι g A).symm
  have Hh := IsOpenImmersion.isPullback h' C.ι j h hhj (by
    rw [hjrange, ← Scheme.Hom.comp_preimage, Scheme.Opens.opensRange_ι])
  have hh' : IsUniversalHomeomorphism h' :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback Hh.flip inferInstance
  refine ⟨U, hηU, hU, A.toScheme, C.toScheme, q', h', inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, hh', ?_, ?_⟩
  · simpa only [h', pullback.lift_snd] using hflat'
  · simpa only [h', pullback.lift_snd] using hfp'

end AlgebraicGeometry
