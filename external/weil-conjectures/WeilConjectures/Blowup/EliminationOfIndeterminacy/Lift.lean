/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Transporting a partial extension along a lift over an open of the base

A partial extension over an open of the base, with closed graph, is transported along a lift of
the global blow-up to the local one (`AlgebraicGeometry.exists_extend_of_lift`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section Statement

variable {X : Scheme.{u}}

/-- **Transporting a partial extension along a lift over an open of the base.** Let
`p : Y ⟶ X` and `π : X' ⟶ X` be morphisms, let `V` be an open of `X` and let
`b : Bl ⟶ V` be a scheme over `V` receiving a lift `ρ` of `π` over `V`. An extension
`g : W ⟶ p ⁻¹ᵁ V` of the restriction `fV` of `f : U ⟶ Y`, defined on an open `W` of `Bl`
containing the inverse image of `U`, pulls back along `ρ` to an open `W'` of `X'`
contained in `π ⁻¹ᵁ V` and containing `π ⁻¹ᵁ U ⊓ π ⁻¹ᵁ V`, together with a morphism
`G : W' ⟶ Y` over `X` which agrees with `f` wherever both are defined and whose graph,
seen inside `Y ×_X X'`, is closed above `V`.

This is the transport step in the proof of Conrad's Theorem 2.4, Case 2: `X'` is the
blow-up of the global center, `Bl` the blow-up of the local center over the affine open
`V`, and `ρ` the canonical comparison morphism. The closedness of the graph above `V` is
obtained by exhibiting the graph of `G` above `V` as a base change of the graph of `g`
along the comparison morphism of the two pullbacks, so that it is again a closed
immersion. -/
theorem exists_extend_of_lift {X X' Y Bl : Scheme.{u}} {p : Y ⟶ X} {π : X' ⟶ X}
    {U V : X.Opens} {f : U.toScheme ⟶ Y}
    {b : Bl ⟶ V.toScheme} {ρ : (π ⁻¹ᵁ V).toScheme ⟶ Bl} (hρ : ρ ≫ b = π ∣_ V)
    {W : Bl.Opens} (hUW : b ⁻¹ᵁ (V.ι ⁻¹ᵁ U) ≤ W)
    {g : W.toScheme ⟶ (p ⁻¹ᵁ V).toScheme} (hg : g ≫ (p ∣_ V) = W.ι ≫ b)
    {fV : (V.ι ⁻¹ᵁ U).toScheme ⟶ (p ⁻¹ᵁ V).toScheme}
    (hfV : fV ≫ (p ⁻¹ᵁ V).ι = (V.ι ∣_ U) ≫ f)
    (hagree : Bl.homOfLE hUW ≫ g = (b ∣_ (V.ι ⁻¹ᵁ U)) ≫ fV)
    (hclosed : IsClosed (Set.range (pullback.lift g W.ι hg))) :
    ∃ (W' : X'.Opens) (_ : W' ≤ π ⁻¹ᵁ V) (G : W'.toScheme ⟶ Y)
      (hG : G ≫ p = W'.ι ≫ π),
      π ⁻¹ᵁ U ⊓ π ⁻¹ᵁ V ≤ W' ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ W'.toScheme) (m : T ⟶ U.toScheme),
          m ≫ U.ι = t ≫ W'.ι ≫ π → t ≫ G = m ≫ f) ∧
      IsClosed (⇑((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι ⁻¹'
        Set.range (pullback.lift G W'.ι hG)) := by
  have hW' : (π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W) ≤ π ⁻¹ᵁ V := (π ⁻¹ᵁ V).ι_image_le _
  have hεinv : ((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ⁻¹ᵁ W).ι = X'.homOfLE hW' :=
    (π ⁻¹ᵁ V).isoImage_ι_inv_ι _
  have he : (((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ W.ι =
      X'.homOfLE hW' ≫ ρ := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hεinv]
  have key : ρ ≫ b ≫ V.ι = (π ⁻¹ᵁ V).ι ≫ π := by
    rw [← Category.assoc, hρ, morphismRestrict_ι]
  have hpt : ∀ y : (π ⁻¹ᵁ V).toScheme, V.ι (b (ρ y)) = π y.1 := by
    intro y
    have h := congr($key y)
    simpa [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply] using h
  have hg' : g ≫ (p ⁻¹ᵁ V).ι ≫ p = W.ι ≫ b ≫ V.ι := by
    rw [← morphismRestrict_ι p V, ← Category.assoc, hg, Category.assoc]
  have hG'' : ((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι) ≫ p = ((ρ ⁻¹ᵁ W).ι ≫ (π ⁻¹ᵁ V).ι) ≫ π := by
    calc ((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι) ≫ p
        = (ρ ∣_ W) ≫ (g ≫ (p ⁻¹ᵁ V).ι ≫ p) := by simp only [Category.assoc]
      _ = ((ρ ∣_ W) ≫ W.ι) ≫ b ≫ V.ι := by rw [hg']; simp only [Category.assoc]
      _ = (ρ ⁻¹ᵁ W).ι ≫ (ρ ≫ b ≫ V.ι) := by
          rw [morphismRestrict_ι]; simp only [Category.assoc]
      _ = ((ρ ⁻¹ᵁ W).ι ≫ (π ⁻¹ᵁ V).ι) ≫ π := by rw [key]; simp only [Category.assoc]
  have hG : ((((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ g ≫ (p ⁻¹ᵁ V).ι) ≫ p =
      ((π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W)).ι ≫ π := by
    calc ((((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ g ≫ (p ⁻¹ᵁ V).ι) ≫ p
        = ((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫
            (((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι) ≫ p) := by simp only [Category.assoc]
      _ = (((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ⁻¹ᵁ W).ι) ≫ (π ⁻¹ᵁ V).ι ≫ π := by
          rw [hG'']; simp only [Category.assoc]
      _ = ((π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W)).ι ≫ π := by
          rw [hεinv, ← Category.assoc, Scheme.homOfLE_ι]
  refine ⟨_, hW', _, hG, ?_, ?_, ?_⟩
  -- the inverse image of `U ⊓ V` is contained in the extension locus
  · intro z hz
    have hzV : z ∈ π ⁻¹ᵁ V := hz.2
    have h1 : V.ι (b (ρ (⟨z, hzV⟩ : (π ⁻¹ᵁ V).toScheme))) ∈ U := by
      rw [hpt ⟨z, hzV⟩]
      exact hz.1
    have hmem : (⟨z, hzV⟩ : (π ⁻¹ᵁ V).toScheme) ∈ ρ ⁻¹ᵁ W := hUW h1
    exact (Scheme.Opens.mem_ι_image_iff (x := (⟨z, hzV⟩ : (π ⁻¹ᵁ V).toScheme))).mpr hmem
  -- the extension agrees with `f` wherever both are defined
  · intro T t m hmt
    have hw' : m ≫ U.ι = (t ≫ X'.homOfLE hW' ≫ ρ ≫ b) ≫ V.ι := by
      rw [hmt]
      calc t ≫ ((π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W)).ι ≫ π
          = t ≫ (X'.homOfLE hW' ≫ (π ⁻¹ᵁ V).ι) ≫ π := by
            rw [Scheme.homOfLE_ι]
        _ = t ≫ X'.homOfLE hW' ≫ (ρ ≫ b ≫ V.ι) := by
            rw [key]; simp only [Category.assoc]
        _ = (t ≫ X'.homOfLE hW' ≫ ρ ≫ b) ≫ V.ι := by simp only [Category.assoc]
    obtain ⟨k, hkfst, hksnd⟩ :
        ∃ k : T ⟶ (V.ι ⁻¹ᵁ U).toScheme, k ≫ (V.ι ∣_ U) = m ∧
          k ≫ (V.ι ⁻¹ᵁ U).ι = t ≫ X'.homOfLE hW' ≫ ρ ≫ b :=
      ⟨(isPullback_morphismRestrict V.ι U).lift _ _ hw',
        (isPullback_morphismRestrict V.ι U).lift_fst _ _ hw',
        (isPullback_morphismRestrict V.ι U).lift_snd _ _ hw'⟩
    obtain ⟨c, hcfst, hcsnd⟩ :
        ∃ c : T ⟶ (b ⁻¹ᵁ (V.ι ⁻¹ᵁ U)).toScheme, c ≫ (b ∣_ (V.ι ⁻¹ᵁ U)) = k ∧
          c ≫ (b ⁻¹ᵁ (V.ι ⁻¹ᵁ U)).ι = t ≫ X'.homOfLE hW' ≫ ρ :=
      ⟨(isPullback_morphismRestrict b (V.ι ⁻¹ᵁ U)).lift _ _
          (by rw [hksnd]; simp only [Category.assoc]),
        (isPullback_morphismRestrict b (V.ι ⁻¹ᵁ U)).lift_fst _ _ _,
        (isPullback_morphismRestrict b (V.ι ⁻¹ᵁ U)).lift_snd _ _ _⟩
    have hcW : c ≫ Bl.homOfLE hUW =
        t ≫ (((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) := by
      rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, hcsnd, Category.assoc, he]
    calc t ≫ ((((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ g ≫ (p ⁻¹ᵁ V).ι)
        = (c ≫ Bl.homOfLE hUW) ≫ g ≫ (p ⁻¹ᵁ V).ι := by
          rw [hcW]; simp only [Category.assoc]
      _ = c ≫ ((b ∣_ (V.ι ⁻¹ᵁ U)) ≫ fV) ≫ (p ⁻¹ᵁ V).ι := by
          rw [← hagree]; simp only [Category.assoc]
      _ = k ≫ (fV ≫ (p ⁻¹ᵁ V).ι) := by rw [← hcfst]; simp only [Category.assoc]
      _ = (k ≫ (V.ι ∣_ U)) ≫ f := by rw [hfV]; simp only [Category.assoc]
      _ = m ≫ f := by rw [hkfst]
  -- the graph is closed over `V`
  · -- the local graph is a closed immersion
    have hpreΓl : IsPreimmersion (pullback.lift g W.ι hg) := by
      have h : IsPreimmersion ((pullback.lift g W.ι hg) ≫ pullback.snd (p ∣_ V) b) := by
        rw [pullback.lift_snd]; infer_instance
      exact IsPreimmersion.of_comp' _ (pullback.snd (p ∣_ V) b)
    have hciΓl : IsClosedImmersion (pullback.lift g W.ι hg) := .of_isPreimmersion _ hclosed
    -- the locus of `Y ×_X X'` above `V` is `(π ⁻¹ᵁ V) ×_X Y`
    have hS : IsPullback ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V))
        (((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι ≫ pullback.fst p π) ((π ⁻¹ᵁ V).ι ≫ π) p :=
      (isPullback_morphismRestrict (pullback.snd p π) (π ⁻¹ᵁ V)).paste_vert
        (IsPullback.of_hasPullback p π).flip
    have hwu : (((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V)) ≫ V.ι =
        (((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι ≫ pullback.fst p π) ≫ p := by
      rw [Category.assoc, morphismRestrict_ι]; exact hS.w
    obtain ⟨u, hufst, husnd⟩ :
        ∃ u : ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).toScheme ⟶ (p ⁻¹ᵁ V).toScheme,
          u ≫ (p ⁻¹ᵁ V).ι = ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι ≫ pullback.fst p π ∧
          u ≫ (p ∣_ V) = ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) ≫ (π ∣_ V) :=
      ⟨(isPullback_morphismRestrict p V).lift _ _ hwu,
        (isPullback_morphismRestrict p V).lift_snd _ _ hwu,
        (isPullback_morphismRestrict p V).lift_fst _ _ hwu⟩
    have hs2 : IsPullback ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) u (π ∣_ V) (p ∣_ V) := by
      refine IsPullback.of_bot ?_ husnd.symm (isPullback_morphismRestrict p V)
      rw [hufst, morphismRestrict_ι]
      exact hS
    obtain ⟨Θ, hΘfst, hΘsnd⟩ :
        ∃ Θ : ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).toScheme ⟶ pullback (p ∣_ V) b,
          Θ ≫ pullback.fst (p ∣_ V) b = u ∧
          Θ ≫ pullback.snd (p ∣_ V) b = ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) ≫ ρ := by
      refine ⟨pullback.lift u (((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) ≫ ρ) ?_,
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
      rw [husnd, Category.assoc, hρ]
    have hK : IsPullback ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) Θ ρ (pullback.snd (p ∣_ V) b) := by
      refine IsPullback.of_bot ?_ hΘsnd.symm (IsPullback.of_hasPullback (p ∣_ V) b).flip
      rw [hΘfst, hρ]
      exact hs2
    obtain ⟨Γ₀, hΓ₀fst, hΓ₀snd⟩ :
        ∃ Γ₀ : (ρ ⁻¹ᵁ W).toScheme ⟶ ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).toScheme,
          Γ₀ ≫ ((pullback.snd p π) ∣_ (π ⁻¹ᵁ V)) = (ρ ⁻¹ᵁ W).ι ∧
          Γ₀ ≫ ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι =
            pullback.lift ((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι) ((ρ ⁻¹ᵁ W).ι ≫ (π ⁻¹ᵁ V).ι) hG'' :=
      ⟨(isPullback_morphismRestrict (pullback.snd p π) (π ⁻¹ᵁ V)).lift _ _
          (pullback.lift_snd _ _ _).symm,
        IsPullback.lift_fst _ _ _ _, IsPullback.lift_snd _ _ _ _⟩
    have hsq : IsPullback Γ₀ (ρ ∣_ W) Θ (pullback.lift g W.ι hg) := by
      refine IsPullback.of_right ?_ ?_ hK
      · rw [hΓ₀fst, pullback.lift_snd]
        exact (isPullback_morphismRestrict ρ W).flip
      · apply pullback.hom_ext
        · rw [Category.assoc, hΘfst, Category.assoc, pullback.lift_fst,
            ← cancel_mono (p ⁻¹ᵁ V).ι, Category.assoc, hufst, Category.assoc,
            ← Category.assoc Γ₀, hΓ₀snd, pullback.lift_fst]
        · rw [Category.assoc, hΘsnd, Category.assoc, pullback.lift_snd, ← Category.assoc,
            hΓ₀fst, morphismRestrict_ι]
    have hciΓ₀ : IsClosedImmersion Γ₀ :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hciΓl
    have hclosed₀ : IsClosed (Set.range Γ₀) := Γ₀.isClosedEmbedding.isClosed_range
    -- the two graphs have the same range
    have hΓeq : ((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫
        pullback.lift ((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι) ((ρ ⁻¹ᵁ W).ι ≫ (π ⁻¹ᵁ V).ι) hG'' =
        pullback.lift ((((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ g ≫ (p ⁻¹ᵁ V).ι)
          ((π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W)).ι hG := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
        simp only [Category.assoc]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, hεinv,
          Scheme.homOfLE_ι]
    have hr : Set.range ⇑(pullback.lift
          ((((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv ≫ (ρ ∣_ W)) ≫ g ≫ (p ⁻¹ᵁ V).ι)
          ((π ⁻¹ᵁ V).ι ''ᵁ (ρ ⁻¹ᵁ W)).ι hG) =
        Set.range ⇑(pullback.lift ((ρ ∣_ W) ≫ g ≫ (p ⁻¹ᵁ V).ι)
          ((ρ ⁻¹ᵁ W).ι ≫ (π ⁻¹ᵁ V).ι) hG'') := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro _ ⟨x, rfl⟩
        refine ⟨((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).inv x, ?_⟩
        rw [← Scheme.Hom.comp_apply, hΓeq]
      · rintro _ ⟨y, rfl⟩
        refine ⟨((π ⁻¹ᵁ V).ι.isoImage (ρ ⁻¹ᵁ W)).hom y, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← hΓeq, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [hr, ← hΓ₀snd]
    have hcoe : Set.range ⇑(Γ₀ ≫ ((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι) =
        ⇑((pullback.snd p π) ⁻¹ᵁ (π ⁻¹ᵁ V)).ι '' Set.range ⇑Γ₀ := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun x ↦ Scheme.Hom.comp_apply _ _ _)
    rw [hcoe, Set.preimage_image_eq _
      ((pullback.snd p π ⁻¹ᵁ (π ⁻¹ᵁ V)).ι.isOpenEmbedding.injective)]
    exact hclosed₀

end Statement

end AlgebraicGeometry
