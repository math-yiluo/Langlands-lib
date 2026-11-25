/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Blowup.Density
public import WeilConjectures.Blowup.EliminationOfIndeterminacy.AffineSpace
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Elimination of indeterminacy for a quasi-affine target over an affine base

Conrad's Theorem 2.4, Case 1: a quasi-affine target of finite type over an affine base
(`AlgebraicGeometry.exists_isAdmissible_extend_of_isQuasiAffine`).
(Blueprint: `lemma:nagata-conrad-quasi-affine-affine-base`.)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry
section Statement

variable {X : Scheme.{u}}

/-- **Conrad's Theorem 2.4, Case 1: a quasi-affine target over an affine base**
(blueprint: `lemma:nagata-conrad-quasi-affine-affine-base`).

Over an affine base, the quasi-affineness of `Y` as a scheme is the same as the
quasi-affineness of `p` as a morphism, so this is the absolute form of the hypothesis.

The proof embeds `Y` into a relative affine space over `X`
(`exists_immersion_affineSpace_of_quasiAffine'`, Stacks Tag 04II), extends `f` there by
`exists_isAdmissible_extend_affineSpace`, makes the preimage of `U` scheme-theoretically
dense by one further blow-up
(`IsAdmissible.exists_comp_isSchemeTheoreticallyDominant_preimage`), and descends the
extension back to `Y` along the closed-immersion part of the immersion, using that a
morphism agreeing on a scheme-theoretically dense open with one factoring through a closed
subscheme factors through it as well. -/
theorem exists_isAdmissible_extend_of_isQuasiAffine [IsAffine X]
    {U : X.Opens} (hU : IsCompact (U : Set X)) {Y : Scheme.{u}} [Y.IsQuasiAffine]
    {p : Y ⟶ X} [LocallyOfFiniteType p]
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι) :
    ∃ (B : IsAdmissible X U) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) ∧
        IsSchemeTheoreticallyDominant (B.I.blowupMap ⁻¹ᵁ U).ι := by
  -- Step 1: an immersion of `Y` into a relative affine space over `X`
  obtain ⟨σ, hσ, i, hi, hiimm⟩ := exists_immersion_affineSpace_of_quasiAffine' p
  -- Step 2: extend `f ≫ i` into affine space after one admissible blow-up
  obtain ⟨B₀, W₀, hW₀, F₀, hF₀, hagree₀, hclosed₀⟩ :=
    exists_isAdmissible_extend_affineSpace hU (f ≫ i) (by rw [Category.assoc, hi, hf])
  -- Step 3: a further blow-up making `U` scheme-theoretically dense
  obtain ⟨B, hh, hcomm, hdense⟩ := B₀.exists_comp_isSchemeTheoreticallyDominant_preimage hU
  -- transport the extension along `hh`
  have hpre : B.I.blowupMap ⁻¹ᵁ U = hh ⁻¹ᵁ (B₀.I.blowupMap ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, hcomm]
  have hUW₁ : B.I.blowupMap ⁻¹ᵁ U ≤ hh ⁻¹ᵁ W₀ := by
    rw [hpre]; exact hh.preimage_mono hW₀
  have hF₁ : ((hh ∣_ W₀) ≫ F₀) ≫ 𝔸(σ; X) ↘ X = (hh ⁻¹ᵁ W₀).ι ≫ B.I.blowupMap := by
    rw [Category.assoc, hF₀, ← Category.assoc, morphismRestrict_ι, Category.assoc, hcomm]
  -- the comparison of the preimages of `U`
  have hk : (B.I.blowup.homOfLE (le_of_eq hpre) ≫ (hh ∣_ (B₀.I.blowupMap ⁻¹ᵁ U))) ≫
      (B₀.I.blowupMap ⁻¹ᵁ U).ι = (B.I.blowupMap ⁻¹ᵁ U).ι ≫ hh := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]
  have hkrestrict : (B.I.blowup.homOfLE (le_of_eq hpre) ≫ (hh ∣_ (B₀.I.blowupMap ⁻¹ᵁ U))) ≫
      (B₀.I.blowupMap ∣_ U) = B.I.blowupMap ∣_ U := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hk,
      Category.assoc, hcomm, morphismRestrict_ι]
  have hstep : B.I.blowup.homOfLE hUW₁ ≫ (hh ∣_ W₀) =
      (B.I.blowup.homOfLE (le_of_eq hpre) ≫ (hh ∣_ (B₀.I.blowupMap ⁻¹ᵁ U))) ≫
        B₀.I.blowup.homOfLE hW₀ := by
    rw [← cancel_mono W₀.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      Scheme.homOfLE_ι, ← Category.assoc, Scheme.homOfLE_ι, hk]
  have hagree₁ : B.I.blowup.homOfLE hUW₁ ≫ ((hh ∣_ W₀) ≫ F₀) =
      (B.I.blowupMap ∣_ U) ≫ (f ≫ i) := by
    rw [← Category.assoc, hstep, Category.assoc, hagree₀, ← Category.assoc, hkrestrict]
  -- Step 4: descend from affine space to `Y` along the closed part of the immersion `i`
  obtain ⟨W, hWW₁, F', hF'ι, hWmem⟩ :=
    exists_opens_restrict_preimage (hh ⁻¹ᵁ W₀) ((hh ∣_ W₀) ≫ F₀) i.coborderRange
  have hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W := by
    intro x hx
    have hxW₁ : x ∈ hh ⁻¹ᵁ W₀ := hUW₁ hx
    rw [hWmem ⟨x, hxW₁⟩]
    have hev : ((hh ∣_ W₀) ≫ F₀) ⟨x, hxW₁⟩ = i (f ((B.I.blowupMap ∣_ U) ⟨x, hx⟩)) := by
      rw [← Scheme.homOfLE_apply' hUW₁ x hx, ← Scheme.Hom.comp_apply, hagree₁,
        Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    rw [hev]
    exact subset_coborder (Set.mem_range_self _)
  -- `U` is scheme-theoretically dense in the blow-up, hence in `W`
  have := B.isProper_blowupMap
  have : CompactSpace B.I.blowup := QuasiCompact.compactSpace_of_compactSpace B.I.blowupMap
  have : QuasiSeparatedSpace B.I.blowup := quasiSeparatedSpace_of_quasiSeparated B.I.blowupMap
  have hUc : IsCompact ((B.I.blowupMap ⁻¹ᵁ U : B.I.blowup.Opens) : Set B.I.blowup) :=
    QuasiCompact.isCompact_preimage (f := B.I.blowupMap) _ U.isOpen hU
  have : QuasiCompact (B.I.blowupMap ⁻¹ᵁ U).ι := Scheme.Opens.quasiCompact_ι _ hUc
  have := hdense
  have : IsSchemeTheoreticallyDominant (B.I.blowup.homOfLE hUW) :=
    IsSchemeTheoreticallyDominant.homOfLE hUW
  -- the restriction of the extension to `U` factors through `Y`
  have hd : B.I.blowup.homOfLE hUW ≫ F' = ((B.I.blowupMap ∣_ U) ≫ f) ≫ i.liftCoborder := by
    rw [← cancel_mono i.coborderRange.ι, Category.assoc, hF'ι, Category.assoc,
      Scheme.Hom.liftCoborder_ι, ← Category.assoc, Scheme.homOfLE_homOfLE, hagree₁,
      Category.assoc]
  have hker : i.liftCoborder.ker ≤ F'.ker := by
    have h1 : i.liftCoborder.ker ≤ (B.I.blowup.homOfLE hUW ≫ F').ker := by
      rw [hd]; exact Scheme.Hom.le_ker_comp _ _
    rwa [Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant] at h1
  have hgj : IsClosedImmersion.lift i.liftCoborder F' hker ≫ i.liftCoborder = F' :=
    IsClosedImmersion.lift_fac _ _ _
  have hgi : IsClosedImmersion.lift i.liftCoborder F' hker ≫ i =
      B.I.blowup.homOfLE hWW₁ ≫ (hh ∣_ W₀) ≫ F₀ := by
    calc IsClosedImmersion.lift i.liftCoborder F' hker ≫ i
        = (IsClosedImmersion.lift i.liftCoborder F' hker ≫ i.liftCoborder) ≫
            i.coborderRange.ι := by rw [Category.assoc, Scheme.Hom.liftCoborder_ι]
      _ = F' ≫ i.coborderRange.ι := by rw [hgj]
      _ = _ := hF'ι
  have hg : IsClosedImmersion.lift i.liftCoborder F' hker ≫ p = W.ι ≫ B.I.blowupMap := by
    rw [← hi, ← Category.assoc, hgi, Category.assoc, hF₁, ← Category.assoc, Scheme.homOfLE_ι]
  refine ⟨B, W, hUW, IsClosedImmersion.lift i.liftCoborder F' hker, hg, ?_, ?_, hdense⟩
  · rw [← cancel_mono i.liftCoborder, Category.assoc, hgj, hd]
  · -- the graph of the extension is closed
    have e₁ : B.I.blowupMap ≫ 𝟙 X = hh ≫ B₀.I.blowupMap := by rw [Category.comp_id, hcomm]
    have e₂ : (𝔸(σ; X) ↘ X) ≫ 𝟙 X = 𝟙 (𝔸(σ; X)) ≫ (𝔸(σ; X) ↘ X) := by
      rw [Category.comp_id, Category.id_comp]
    have e₃ : B.I.blowupMap ≫ 𝟙 X = 𝟙 B.I.blowup ≫ B.I.blowupMap := by
      rw [Category.comp_id, Category.id_comp]
    have e₄ : p ≫ 𝟙 X = i ≫ 𝔸(σ; X) ↘ X := by rw [Category.comp_id, hi]
    set Γ₀ := pullback.lift W₀.ι F₀ hF₀.symm with hΓ₀
    set Γ₁ := pullback.lift (hh ⁻¹ᵁ W₀).ι ((hh ∣_ W₀) ≫ F₀) hF₁.symm with hΓ₁
    set Θ : pullback B.I.blowupMap (𝔸(σ; X) ↘ X) ⟶
        pullback B₀.I.blowupMap (𝔸(σ; X) ↘ X) :=
      pullback.map _ _ _ _ hh (𝟙 _) (𝟙 X) e₁ e₂ with hΘ
    set Θ' : pullback B.I.blowupMap p ⟶ pullback B.I.blowupMap (𝔸(σ; X) ↘ X) :=
      pullback.map _ _ _ _ (𝟙 _) i (𝟙 X) e₃ e₄ with hΘ'
    set Γ' := pullback.lift W.ι (IsClosedImmersion.lift i.liftCoborder F' hker) hg.symm with hΓ'
    -- the graph over `W₀` is a closed immersion
    have : IsPreimmersion (Γ₀ ≫ pullback.fst B₀.I.blowupMap (𝔸(σ; X) ↘ X)) := by
      rw [hΓ₀, pullback.lift_fst]; infer_instance
    have : IsPreimmersion Γ₀ :=
      IsPreimmersion.of_comp' Γ₀ (pullback.fst B₀.I.blowupMap (𝔸(σ; X) ↘ X))
    have : IsClosedImmersion Γ₀ := IsClosedImmersion.of_isPreimmersion _ hclosed₀
    -- the two auxiliary pullback squares
    have hbot : IsPullback (pullback.fst B.I.blowupMap (𝔸(σ; X) ↘ X)) Θ hh
        (pullback.fst B₀.I.blowupMap (𝔸(σ; X) ↘ X)) := by
      refine IsPullback.of_bot (t := IsPullback.of_hasPullback _ _) ?_ (by simp [hΘ])
      have h1 : Θ ≫ pullback.snd B₀.I.blowupMap (𝔸(σ; X) ↘ X) =
          pullback.snd B.I.blowupMap (𝔸(σ; X) ↘ X) := by simp [hΘ]
      rw [h1, hcomm]
      exact IsPullback.of_hasPullback _ _
    have hbot' : IsPullback (pullback.snd B.I.blowupMap p) Θ' i
        (pullback.snd B.I.blowupMap (𝔸(σ; X) ↘ X)) := by
      refine IsPullback.of_bot (t := (IsPullback.of_hasPullback _ _).flip) ?_ (by simp [hΘ'])
      have h1 : Θ' ≫ pullback.fst B.I.blowupMap (𝔸(σ; X) ↘ X) =
          pullback.fst B.I.blowupMap p := by simp [hΘ']
      rw [h1, hi]
      exact (IsPullback.of_hasPullback _ _).flip
    have : IsImmersion Θ' := MorphismProperty.of_isPullback (P := @IsImmersion) hbot' inferInstance
    -- the graph over `W₁` is a base change of the graph over `W₀`
    have hsq : IsPullback Γ₁ (hh ∣_ W₀) Θ Γ₀ := by
      refine IsPullback.of_right ?_ ?_ hbot
      · have a1 : Γ₁ ≫ pullback.fst B.I.blowupMap (𝔸(σ; X) ↘ X) = (hh ⁻¹ᵁ W₀).ι := by
          rw [hΓ₁, pullback.lift_fst]
        have a2 : Γ₀ ≫ pullback.fst B₀.I.blowupMap (𝔸(σ; X) ↘ X) = W₀.ι := by
          rw [hΓ₀, pullback.lift_fst]
        rw [a1, a2]
        exact (isPullback_morphismRestrict hh W₀).flip
      · apply pullback.hom_ext <;> simp [hΓ₀, hΓ₁, hΘ]
    have : IsClosedImmersion Γ₁ :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip inferInstance
    have hclosed₁ : IsClosed (Set.range Γ₁) := Γ₁.isClosedEmbedding.isClosed_range
    -- the graph over `W` is the preimage of the graph over `W₁`
    have hΓ'Θ' : Γ' ≫ Θ' = B.I.blowup.homOfLE hWW₁ ≫ Γ₁ := by
      apply pullback.hom_ext <;> simp [hΓ', hΓ₁, hΘ', hgi]
    have hinj : Function.Injective Θ'.base := Θ'.isEmbedding.injective
    have hsnd₁ : ∀ x, pullback.snd B.I.blowupMap (𝔸(σ; X) ↘ X) (Γ₁ x) =
        ((hh ∣_ W₀) ≫ F₀) x := by
      intro x; rw [← Scheme.Hom.comp_apply, hΓ₁, pullback.lift_snd]
    have hsndΘ' : ∀ x, pullback.snd B.I.blowupMap (𝔸(σ; X) ↘ X) (Θ' x) =
        i (pullback.snd B.I.blowupMap p x) := by
      intro x
      rw [← Scheme.Hom.comp_apply, hΘ', pullback.lift_snd, Scheme.Hom.comp_apply]
    have hrange : Set.range Γ'.base = Θ'.base ⁻¹' (Set.range Γ₁.base) := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨B.I.blowup.homOfLE hWW₁ w, by rw [← Scheme.Hom.comp_apply, ← hΓ'Θ',
          Scheme.Hom.comp_apply]⟩
      · rintro ⟨w', hw'⟩
        have hFw : ((hh ∣_ W₀) ≫ F₀) w' = i (pullback.snd B.I.blowupMap p z) := by
          rw [← hsnd₁, hw', hsndΘ']
        have hwW : w'.1 ∈ W := by
          rw [hWmem w', hFw]
          exact subset_coborder (Set.mem_range_self _)
        refine ⟨⟨w'.1, hwW⟩, hinj ?_⟩
        rw [← Scheme.Hom.comp_apply, hΓ'Θ', Scheme.Hom.comp_apply,
          show B.I.blowup.homOfLE hWW₁ ⟨w'.1, hwW⟩ = w' from Subtype.ext (by simp)]
        exact hw'
    have hclosedΓ' : IsClosed (Set.range Γ'.base) := by
      rw [hrange]; exact hclosed₁.preimage Θ'.continuous
    have : IsPreimmersion (Γ' ≫ pullback.fst B.I.blowupMap p) := by
      rw [hΓ', pullback.lift_fst]; infer_instance
    have : IsPreimmersion Γ' := IsPreimmersion.of_comp' Γ' (pullback.fst B.I.blowupMap p)
    have : IsClosedImmersion Γ' := IsClosedImmersion.of_isPreimmersion _ hclosedΓ'
    have hflip : pullback.lift (IsClosedImmersion.lift i.liftCoborder F' hker) W.ι hg =
        Γ' ≫ (pullbackSymmetry B.I.blowupMap p).hom := by
      apply pullback.hom_ext <;> simp [hΓ']
    rw [hflip]
    exact (Γ' ≫ (pullbackSymmetry B.I.blowupMap p).hom).isClosedEmbedding.isClosed_range

end Statement

end AlgebraicGeometry
