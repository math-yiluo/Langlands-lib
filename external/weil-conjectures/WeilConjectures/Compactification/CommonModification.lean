/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Density
public import WeilConjectures.Blowup.Extension
public import WeilConjectures.Compactification.EliminationOfIndeterminacy
public import WeilConjectures.Compactification.StrictTransformBlowup
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Pullbacks

/-!

# Common modifications of two models

This file constructs the **common modification of two models** (Stacks Project Tag 0F3X;
blueprint `def:common-modification`, `thm:0F3X`, `def:nagata-common-modification`,
`lemma:nagata-common-modification`; proof order item 32):

- `AlgebraicGeometry.CommonModification`: the data of a common modification of two
  separated finite-type models `X₁`, `X₂` of a common open `U` over `S`;
- `AlgebraicGeometry.nonempty_commonModification`: two such models admit `U`-admissible
  blow-ups which glue along a common copy of the modified `U`-locus to a separated
  finite-type model;
- `AlgebraicGeometry.CommonModification.j`: the open immersion of `U` into the glued
  scheme, and `AlgebraicGeometry.CommonModification.dense_range_j`: density of `U` is
  transported through the common modification (blueprint:
  `lemma:nagata-two-open-density-transport`).

The extension step of the construction is recorded separately as

- `AlgebraicGeometry.IsAdmissible.exists_isOpenImmersion_blowup`: a further finite-type
  blow-up of the strict transform of a morphism `p` along a `U`-admissible blow-up sits,
  as an open subscheme, inside a single `U`-admissible blow-up of the base.

This combines Stacks Project Tag 080E (the strict transform is the blow-up of the
pulled-back centre) with the extension and composition of admissible centres.

Everything here rests on elimination of indeterminacy
(`WeilConjectures.Compactification.EliminationOfIndeterminacy`, Tag 081S).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section CommonModification

variable {S U X₁ X₂ : Scheme.{u}}

/-- The data of a **common modification** of two separated finite-type models `X₁`,
`X₂` of a common open `U` over `S` (Stacks Project Tag 0F3X; blueprint:
`def:nagata-common-modification`). -/
structure CommonModification (s₁ : X₁ ⟶ S) (s₂ : X₂ ⟶ S) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] where
  /-- The `U`-admissible blow-up of the first model. -/
  B₁ : IsAdmissible X₁ j₁.opensRange
  /-- The `U`-admissible blow-up of the second model. -/
  B₂ : IsAdmissible X₂ j₂.opensRange
  /-- The glued common modification. -/
  W : Scheme.{u}
  /-- The structure morphism of the common modification. -/
  w : W ⟶ S
  /-- The open immersion of the first modified model into the glued scheme. -/
  k₁ : B₁.I.blowup ⟶ W
  /-- The open immersion of the second modified model into the glued scheme. -/
  k₂ : B₂.I.blowup ⟶ W
  /-- The first modified model is an open subscheme of the glued scheme. -/
  isOpenImmersion_k₁ : IsOpenImmersion k₁
  /-- The second modified model is an open subscheme of the glued scheme. -/
  isOpenImmersion_k₂ : IsOpenImmersion k₂
  /-- The first open immersion lies over `S`. -/
  k₁_w : k₁ ≫ w = B₁.I.blowupMap ≫ s₁
  /-- The second open immersion lies over `S`. -/
  k₂_w : k₂ ≫ w = B₂.I.blowupMap ≫ s₂
  /-- The lift of `U` into the first modified model. -/
  u₁ : U ⟶ B₁.I.blowup
  /-- The lift of `U` into the second modified model. -/
  u₂ : U ⟶ B₂.I.blowup
  /-- The first lift of `U` lies over the given open immersion `j₁`. -/
  u₁_blowupMap : u₁ ≫ B₁.I.blowupMap = j₁
  /-- The second lift of `U` lies over the given open immersion `j₂`. -/
  u₂_blowupMap : u₂ ≫ B₂.I.blowupMap = j₂
  /-- The two copies of `U` in the glued scheme agree. -/
  u_glue : u₁ ≫ k₁ = u₂ ≫ k₂
  /-- The two modified models cover the glued scheme. -/
  cover : Set.range k₁ ∪ Set.range k₂ = Set.univ
  /-- The glued scheme is separated over `S`. -/
  isSeparated_w : IsSeparated w
  /-- The glued scheme is locally of finite type over `S`. -/
  locallyOfFiniteType_w : LocallyOfFiniteType w
  /-- The glued scheme is quasi-compact over `S`. -/
  quasiCompact_w : QuasiCompact w

attribute [instance] CommonModification.isOpenImmersion_k₁
  CommonModification.isOpenImmersion_k₂ CommonModification.isSeparated_w
  CommonModification.locallyOfFiniteType_w CommonModification.quasiCompact_w

/-- **A blow-up of the strict transform extends to an admissible blow-up of the base**
(the second half of the construction of Stacks Project Tag 0F3X). Let `X` be qcqs, `U ⊆ X`
an open contained in the range of a quasi-compact morphism `p : V ⟶ X`, and `B` a
`U`-admissible blow-up of `X` whose strict transform of `p` is an open immersion into the
blown-up scheme `X'`. By Stacks Project Tag 080E
(`Scheme.IdealSheafData.exists_blowup_comap_iso_strictTransform`) that strict transform is
the blow-up of `V` at the pulled-back centre `B.I.comap p`, so a further finite-type centre
`M` on it, whose support avoids the locus over `U`, has a blow-up `Bl_M` which is a blow-up
of an open subscheme of `X'`. Extending `M` across that open
(`IsAdmissible.exists_extend`) and composing the two admissible blow-ups
(`IsAdmissible.exists_comp`) exhibits `Bl_M` as an open subscheme of a single
`U`-admissible blow-up of `X`, lying over `V` as prescribed.
(Blueprint: part of `lemma:nagata-common-modification`.) -/
theorem IsAdmissible.exists_isOpenImmersion_blowup {X V : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] {U : X.Opens} (p : V ⟶ X) [QuasiCompact p]
    (hpU : (U : Set X) ⊆ Set.range p) (B : IsAdmissible X U)
    (hB : IsOpenImmersion (strictTransformMap p B.I.blowupMap B.preservedOpen))
    (M : (B.I.comap p).blowup.IdealSheafData) (hM : M.ofFiniteType)
    (hdisj : Disjoint (⇑((B.I.comap p).blowupMap ≫ p) ⁻¹' (U : Set X))
      (M.support : Set (B.I.comap p).blowup)) :
    ∃ (C : IsAdmissible X U) (m : M.blowup ⟶ C.I.blowup), IsOpenImmersion m ∧
      m ≫ C.I.blowupMap = M.blowupMap ≫ (B.I.comap p).blowupMap ≫ p := by
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace p
  have := B.isProper_blowupMap
  have : QuasiCompact B.I.blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap B.finiteType
  have : CompactSpace B.I.blowup := QuasiCompact.compactSpace_of_compactSpace B.I.blowupMap
  have : QuasiSeparatedSpace B.I.blowup := quasiSeparatedSpace_of_quasiSeparated B.I.blowupMap
  have : QuasiCompact (B.I.comap p).blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap (B.finiteType.comap p)
  have : CompactSpace (B.I.comap p).blowup :=
    QuasiCompact.compactSpace_of_compactSpace (B.I.comap p).blowupMap
  -- Tag 080E: the strict transform of `p` is the blow-up of the pulled-back centre, and it
  -- is an open subscheme of `X'` containing the whole locus over `U`.
  obtain ⟨q, hqOI, hq, hqrange⟩ : ∃ q : (B.I.comap p).blowup ⟶ B.I.blowup,
      IsOpenImmersion q ∧ q ≫ B.I.blowupMap = (B.I.comap p).blowupMap ≫ p ∧
      ∀ x' : B.I.blowup, B.I.blowupMap x' ∈ U → x' ∈ Set.range ⇑q := by
    have := hB
    obtain ⟨e, -, he⟩ := B.I.exists_blowup_comap_iso_strictTransform p
    refine ⟨e.hom ≫ strictTransformMap p B.I.blowupMap B.preservedOpen, inferInstance, he,
      fun x' hx' ↦ ?_⟩
    obtain ⟨t, ht⟩ := mem_range_strictTransformMap_of_mem_of_mem_range p B.I.blowupMap
      B.preservedOpen (B.le_preservedOpen hx') (hpU hx')
    have hsurj : Function.Surjective ⇑e.hom := by
      have h := (Scheme.homeoOfIso e).surjective
      rwa [Scheme.coe_homeoOfIso] at h
    obtain ⟨t', rfl⟩ := hsurj t
    exact ⟨t', by rw [Scheme.Hom.comp_apply]; exact ht⟩
  have := hqOI
  -- the strict transform as an open subscheme `T` of `X'`
  set T : B.I.blowup.Opens := q.opensRange with hTdef
  set φ : (B.I.comap p).blowup ≅ T.toScheme := q.isoOpensRange with hφdef
  have hφι : φ.hom ≫ T.ι = q := q.isoOpensRange_hom_ι
  have hφinv : ∀ t : T.toScheme, q (φ.inv t) = T.ι t := by
    intro t
    rw [← hφι, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply φ.inv φ.hom, φ.inv_hom_id]
    simp
  -- transport the centre `M` to the open `T`
  obtain ⟨N, hNft, hNsupp, f, hf⟩ : ∃ N : T.toScheme.IdealSheafData, N.ofFiniteType ∧
      (N.support : Set T.toScheme) = ⇑φ.inv ⁻¹' (M.support : Set (B.I.comap p).blowup) ∧
      ∃ f : N.blowup ≅ M.blowup, f.hom ≫ M.blowupMap = N.blowupMap ≫ φ.inv := by
    obtain ⟨f, hf⟩ := Scheme.IdealSheafData.exists_blowup_comap_iso M φ.symm
    exact ⟨M.comap φ.inv, hM.comap _, by simp, f, hf⟩
  -- the locus over `U` is contained in `T`, and `T` is quasi-compact
  have hUT : B.I.blowupMap ⁻¹ᵁ U ≤ T := fun x' hx' ↦ hqrange x' hx'
  have hTcpt : IsCompact ((T : B.I.blowup.Opens) : Set B.I.blowup) := isCompact_range q.continuous
  -- the support of the transported centre avoids the locus over `U`
  have hdisjN : Disjoint
      ((T.ι ⁻¹ᵁ (B.I.blowupMap ⁻¹ᵁ U) : T.toScheme.Opens) : Set T.toScheme)
      (N.support : Set T.toScheme) := by
    rw [Set.disjoint_left]
    intro t ht htN
    rw [hNsupp] at htN
    refine Set.disjoint_left.mp hdisj ?_ htN
    have hmem : B.I.blowupMap (q (φ.inv t)) ∈ U := by
      rw [hφinv]
      exact ht
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, ← hq, Scheme.Hom.comp_apply]
    exact hmem
  -- extend the centre across `T` and compose the two admissible blow-ups
  obtain ⟨C', h, hh, hpb⟩ := IsAdmissible.exists_extend hTcpt hUT N hNft hdisjN
  have : IsOpenImmersion h := IsOpenImmersion.of_isPullback hpb inferInstance
  obtain ⟨K, hKft, hKdisj, iso, hiso⟩ := IsAdmissible.exists_comp B C'
  refine ⟨⟨K, hKft, hKdisj⟩, f.inv ≫ h ≫ iso.hom, inferInstance, ?_⟩
  have hfinv : f.inv ≫ N.blowupMap = M.blowupMap ≫ φ.hom := by
    rw [← cancel_mono φ.inv, Category.assoc, Category.assoc, φ.hom_inv_id, Category.comp_id,
      ← hf, Iso.inv_hom_id_assoc]
  calc (f.inv ≫ h ≫ iso.hom) ≫ K.blowupMap
      = f.inv ≫ h ≫ C'.I.blowupMap ≫ B.I.blowupMap := by
        rw [Category.assoc, Category.assoc, hiso]
    _ = f.inv ≫ N.blowupMap ≫ T.ι ≫ B.I.blowupMap := by rw [← Category.assoc h, hh,
        Category.assoc]
    _ = M.blowupMap ≫ (φ.hom ≫ T.ι) ≫ B.I.blowupMap := by
        rw [← Category.assoc, hfinv]
        simp only [Category.assoc]
    _ = M.blowupMap ≫ (B.I.comap p).blowupMap ≫ p := by rw [hφι, hq]

/-- **Existence of a common modification** (Stacks Project Tag 0F3X; blueprint:
`lemma:nagata-common-modification`; proof order item 32).

The construction is the one of the blueprint: form the scheme-theoretic image
`X₁₂ ⊆ X₁ ×_S X₂` of `U`, eliminate the indeterminacy of both projections
(`exists_admissibleBlowup_isOpenImmersion_strictTransformMap`), dominate the two center
ideals by their product (`Scheme.IdealSheafData.exists_blowup_mul_iso`) and extend the
resulting common blow-up of `X₁₂` across the open strict transforms. -/
theorem nonempty_commonModification [CompactSpace S] [QuasiSeparatedSpace S]
    (s₁ : X₁ ⟶ S) (s₂ : X₂ ⟶ S) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (hj : j₁ ≫ s₁ = j₂ ≫ s₂)
    [IsSeparated s₁] [LocallyOfFiniteType s₁] [QuasiCompact s₁]
    [IsSeparated s₂] [LocallyOfFiniteType s₂] [QuasiCompact s₂] :
    Nonempty (CommonModification s₁ s₂ j₁ j₂) := by
  -- Step 0: finiteness of the ambient schemes.
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace s₁
  have : CompactSpace X₂ := QuasiCompact.compactSpace_of_compactSpace s₂
  have : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated s₁
  have : QuasiSeparatedSpace X₂ := quasiSeparatedSpace_of_quasiSeparated s₂
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace j₁
  have : IsSeparated (pullback.fst s₁ s₂) := MorphismProperty.pullback_fst _ _ ‹_›
  have : LocallyOfFiniteType (pullback.fst s₁ s₂) := MorphismProperty.pullback_fst _ _ ‹_›
  have : QuasiCompact (pullback.fst s₁ s₂) := MorphismProperty.pullback_fst _ _ ‹_›
  have : IsSeparated (pullback.snd s₁ s₂) := MorphismProperty.pullback_snd _ _ ‹_›
  have : LocallyOfFiniteType (pullback.snd s₁ s₂) := MorphismProperty.pullback_snd _ _ ‹_›
  have : QuasiCompact (pullback.snd s₁ s₂) := MorphismProperty.pullback_snd _ _ ‹_›
  -- Step 1: the graph `γ = (j₁, j₂) : U ⟶ X₁ ×_S X₂`, its scheme-theoretic image `X₁₂`
  -- and the two projections `p₁`, `p₂` of the latter.
  obtain ⟨γ, hγdef⟩ : ∃ g : U ⟶ pullback s₁ s₂, g = pullback.lift j₁ j₂ hj := ⟨_, rfl⟩
  have hγ₁ : γ ≫ pullback.fst s₁ s₂ = j₁ := by rw [hγdef]; exact pullback.lift_fst _ _ _
  have hγ₂ : γ ≫ pullback.snd s₁ s₂ = j₂ := by rw [hγdef]; exact pullback.lift_snd _ _ _
  have : QuasiCompact γ := quasiCompact_of_partialSection s₁ s₂ j₁ γ hγ₁
  obtain ⟨p₁, hp₁def⟩ : ∃ f : γ.image ⟶ X₁, f = γ.imageι ≫ pullback.fst s₁ s₂ := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂def⟩ : ∃ f : γ.image ⟶ X₂, f = γ.imageι ≫ pullback.snd s₁ s₂ := ⟨_, rfl⟩
  have : IsSeparated p₁ := by rw [hp₁def]; infer_instance
  have : LocallyOfFiniteType p₁ := by rw [hp₁def]; infer_instance
  have : QuasiCompact p₁ := by rw [hp₁def]; infer_instance
  have : IsSeparated p₂ := by rw [hp₂def]; infer_instance
  have : LocallyOfFiniteType p₂ := by rw [hp₂def]; infer_instance
  have : QuasiCompact p₂ := by rw [hp₂def]; infer_instance
  have hcomm : p₁ ≫ s₁ = p₂ ≫ s₂ := by
    rw [hp₁def, hp₂def, Category.assoc, Category.assoc, pullback.condition]
  have htoIm₁ : γ.toImage ≫ p₁ = j₁ := by
    rw [hp₁def, ← Category.assoc, Scheme.Hom.toImage_imageι, hγ₁]
  have htoIm₂ : γ.toImage ≫ p₂ = j₂ := by
    rw [hp₂def, ← Category.assoc, Scheme.Hom.toImage_imageι, hγ₂]
  -- Step 2: both projections are isomorphisms over the copies of `U`, whose inverse images
  -- in `X₁₂` are both the range of `γ.toImage`.
  have hiso₁ : IsIso (p₁ ∣_ j₁.opensRange) := by
    rw [hp₁def]; exact isIso_restrict_imageι_comp_fst s₁ s₂ j₁ γ hγ₁
  have hOItoIm : IsOpenImmersion γ.toImage :=
    isOpenImmersion_of_comp_of_isIso_restrict γ.toImage p₁ j₁ htoIm₁ hiso₁
  have hr₁ : Set.range ⇑γ.toImage = ⇑p₁ ⁻¹' Set.range ⇑j₁ :=
    range_eq_preimage_of_comp_of_isIso_restrict γ.toImage p₁ j₁ htoIm₁ hiso₁
  have hr₂ : ⇑p₂ ⁻¹' Set.range ⇑j₂ = Set.range ⇑γ.toImage := by
    rw [hp₂def]; exact preimage_range_snd_eq_range_toImage s₁ s₂ γ j₂ hγ₂
  have hiso₂ : IsIso (p₂ ∣_ j₂.opensRange) := by
    have hinv : j₂.isoOpensRange.inv ≫ j₂ = j₂.opensRange.ι := by
      rw [Iso.inv_comp_eq]
      exact (Scheme.Hom.isoOpensRange_hom_ι j₂).symm
    have hsurj : Function.Surjective ⇑j₂.isoOpensRange.inv := by
      have h := (Scheme.homeoOfIso j₂.isoOpensRange.symm).surjective
      rwa [Scheme.coe_homeoOfIso, Iso.symm_hom] at h
    refine isIso_morphismRestrict_of_range_eq p₂ j₂.opensRange
      (j₂.isoOpensRange.inv ≫ γ.toImage) ?_ ?_
    · rw [Category.assoc, htoIm₂, hinv]
    · rw [show ((p₂ ⁻¹ᵁ j₂.opensRange : γ.image.Opens) : Set γ.image) =
        ⇑p₂ ⁻¹' Set.range ⇑j₂ from rfl, hr₂, Scheme.Hom.comp_base, TopCat.coe_comp,
        Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ]
  -- Step 3: elimination of indeterminacy for both projections (Tag 081S).
  have hU₁ : IsCompact ((j₁.opensRange : X₁.Opens) : Set X₁) := isCompact_range j₁.continuous
  have hU₂ : IsCompact ((j₂.opensRange : X₂.Opens) : Set X₂) := isCompact_range j₂.continuous
  obtain ⟨B₁, hB₁⟩ := exists_admissibleBlowup_isOpenImmersion_strictTransformMap hU₁ p₁ hiso₁
  obtain ⟨B₂, hB₂⟩ := exists_admissibleBlowup_isOpenImmersion_strictTransformMap hU₂ p₂ hiso₂
  have hK₁ft : (B₁.I.comap p₁).ofFiniteType := B₁.finiteType.comap p₁
  have hK₂ft : (B₂.I.comap p₂).ofFiniteType := B₂.finiteType.comap p₂
  have hK₁supp : ((B₁.I.comap p₁).support : Set γ.image) = ⇑p₁ ⁻¹' (B₁.I.support : Set X₁) := by
    simp
  have hK₂supp : ((B₂.I.comap p₂).support : Set γ.image) = ⇑p₂ ⁻¹' (B₂.I.support : Set X₂) := by
    simp
  -- the ranges of the two projections contain the copies of `U`
  have hpU₁ : ((j₁.opensRange : X₁.Opens) : Set X₁) ⊆ Set.range ⇑p₁ := by
    rintro - ⟨t, rfl⟩
    exact ⟨γ.toImage t, by rw [← Scheme.Hom.comp_apply, htoIm₁]⟩
  have hpU₂ : ((j₂.opensRange : X₂.Opens) : Set X₂) ⊆ Set.range ⇑p₂ := by
    rintro - ⟨t, rfl⟩
    exact ⟨γ.toImage t, by rw [← Scheme.Hom.comp_apply, htoIm₂]⟩
  -- Step 4: the common modification of `X₁₂` is the blow-up of the product of the two
  -- pulled-back centres; it dominates both strict transforms.
  obtain ⟨L, hLdef⟩ : ∃ J : γ.image.IdealSheafData, J = (B₁.I.comap p₁) * (B₂.I.comap p₂) :=
    ⟨_, rfl⟩
  have hLft : L.ofFiniteType := by rw [hLdef]; exact hK₁ft.mul hK₂ft
  have hLsupp : (L.support : Set γ.image) =
      ((B₁.I.comap p₁).support : Set γ.image) ∪ ((B₂.I.comap p₂).support : Set γ.image) := by
    rw [hLdef, Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
  obtain ⟨a₁, ha₁⟩ : ∃ e : L.blowup ≅ ((B₂.I.comap p₂).comap (B₁.I.comap p₁).blowupMap).blowup,
      e.hom ≫ ((B₂.I.comap p₂).comap (B₁.I.comap p₁).blowupMap).blowupMap ≫
        (B₁.I.comap p₁).blowupMap = L.blowupMap := by
    rw [hLdef]
    exact Scheme.IdealSheafData.exists_blowup_mul_iso _ _
  obtain ⟨a₂, ha₂⟩ : ∃ e : L.blowup ≅ ((B₁.I.comap p₁).comap (B₂.I.comap p₂).blowupMap).blowup,
      e.hom ≫ ((B₁.I.comap p₁).comap (B₂.I.comap p₂).blowupMap).blowupMap ≫
        (B₂.I.comap p₂).blowupMap = L.blowupMap := by
    rw [hLdef, mul_comm (B₁.I.comap p₁) (B₂.I.comap p₂)]
    exact Scheme.IdealSheafData.exists_blowup_mul_iso _ _
  -- the two auxiliary centres avoid the locus over `U`
  have hdisj₁ : Disjoint
      (⇑((B₁.I.comap p₁).blowupMap ≫ p₁) ⁻¹' ((j₁.opensRange : X₁.Opens) : Set X₁))
      (((B₂.I.comap p₂).comap (B₁.I.comap p₁).blowupMap).support :
        Set (B₁.I.comap p₁).blowup) := by
    rw [Set.disjoint_left]
    intro z hz hzs
    rw [Scheme.IdealSheafData.coe_support_comap, hK₂supp] at hzs
    refine Set.disjoint_left.mp B₂.disjoint_support ?_ hzs
    have hmem : (B₁.I.comap p₁).blowupMap z ∈ ⇑p₁ ⁻¹' Set.range ⇑j₁ := by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]
      exact hz
    rw [← hr₁, ← hr₂] at hmem
    exact hmem
  have hdisj₂ : Disjoint
      (⇑((B₂.I.comap p₂).blowupMap ≫ p₂) ⁻¹' ((j₂.opensRange : X₂.Opens) : Set X₂))
      (((B₁.I.comap p₁).comap (B₂.I.comap p₂).blowupMap).support :
        Set (B₂.I.comap p₂).blowup) := by
    rw [Set.disjoint_left]
    intro z hz hzs
    rw [Scheme.IdealSheafData.coe_support_comap, hK₁supp] at hzs
    refine Set.disjoint_left.mp B₁.disjoint_support ?_ hzs
    have hmem : (B₂.I.comap p₂).blowupMap z ∈ ⇑p₂ ⁻¹' Set.range ⇑j₂ := by
      rw [Set.mem_preimage, ← Scheme.Hom.comp_apply]
      exact hz
    rw [hr₂, hr₁] at hmem
    exact hmem
  -- Step 5: extend both auxiliary blow-ups to `U`-admissible blow-ups of `X₁` and `X₂`,
  -- inside which the common modification `L.blowup` sits as an open subscheme.
  obtain ⟨C₁, m₁, hm₁OI, hm₁⟩ := IsAdmissible.exists_isOpenImmersion_blowup p₁ hpU₁ B₁ hB₁
    ((B₂.I.comap p₂).comap (B₁.I.comap p₁).blowupMap) (hK₂ft.comap _) hdisj₁
  obtain ⟨C₂, m₂, hm₂OI, hm₂⟩ := IsAdmissible.exists_isOpenImmersion_blowup p₂ hpU₂ B₂ hB₂
    ((B₁.I.comap p₁).comap (B₂.I.comap p₂).blowupMap) (hK₁ft.comap _) hdisj₂
  have := hm₁OI
  have := hm₂OI
  obtain ⟨n₁, hn₁def⟩ : ∃ n : L.blowup ⟶ C₁.I.blowup, n = a₁.hom ≫ m₁ := ⟨_, rfl⟩
  obtain ⟨n₂, hn₂def⟩ : ∃ n : L.blowup ⟶ C₂.I.blowup, n = a₂.hom ≫ m₂ := ⟨_, rfl⟩
  have : IsOpenImmersion n₁ := by rw [hn₁def]; infer_instance
  have : IsOpenImmersion n₂ := by rw [hn₂def]; infer_instance
  have hn₁ : n₁ ≫ C₁.I.blowupMap = L.blowupMap ≫ p₁ := by
    rw [hn₁def, Category.assoc, hm₁, ← ha₁]
    simp only [Category.assoc]
  have hn₂ : n₂ ≫ C₂.I.blowupMap = L.blowupMap ≫ p₂ := by
    rw [hn₂def, Category.assoc, hm₂, ← ha₂]
    simp only [Category.assoc]
  -- Step 6: the copy of `U` in the common modification.
  have hdisjU : Disjoint ((γ.toImage.opensRange : γ.image.Opens) : Set γ.image)
      (L.support : Set γ.image) := by
    have hcoe : ((γ.toImage.opensRange : γ.image.Opens) : Set γ.image) =
        Set.range ⇑γ.toImage := rfl
    rw [Set.disjoint_left, hLsupp, hcoe]
    rintro t ht (h | h)
    · rw [hK₁supp] at h
      rw [hr₁] at ht
      exact Set.disjoint_left.mp B₁.disjoint_support ht h
    · rw [hK₂supp] at h
      rw [← hr₂] at ht
      exact Set.disjoint_left.mp B₂.disjoint_support ht h
  have : IsIso (L.blowupMap ∣_ γ.toImage.opensRange) := L.isIso_blowupMap_restrict hdisjU
  obtain ⟨u, hu⟩ : ∃ u : U ⟶ L.blowup, u ≫ L.blowupMap = γ.toImage :=
    ⟨(γ.toImage.isoOpensRange.hom ≫ inv (L.blowupMap ∣_ γ.toImage.opensRange)) ≫
      (L.blowupMap ⁻¹ᵁ γ.toImage.opensRange).ι, by
      simp only [Category.assoc]
      rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, Scheme.Hom.isoOpensRange_hom_ι]⟩
  have hu₁ : (u ≫ n₁) ≫ C₁.I.blowupMap = j₁ := by
    rw [Category.assoc, hn₁, ← Category.assoc, hu, htoIm₁]
  have hu₂ : (u ≫ n₂) ≫ C₂.I.blowupMap = j₂ := by
    rw [Category.assoc, hn₂, ← Category.assoc, hu, htoIm₂]
  -- Step 7: glue `C₁.I.blowup` and `C₂.I.blowup` along the common modification.
  have := C₁.isProper_blowupMap
  have := C₂.isProper_blowupMap
  have : QuasiCompact C₁.I.blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap C₁.finiteType
  have : QuasiCompact C₂.I.blowupMap :=
    Scheme.IdealSheafData.quasiCompact_blowupMap C₂.finiteType
  have hw : n₁ ≫ C₁.I.blowupMap ≫ s₁ = n₂ ≫ C₂.I.blowupMap ≫ s₂ :=
    calc n₁ ≫ C₁.I.blowupMap ≫ s₁ = (n₁ ≫ C₁.I.blowupMap) ≫ s₁ := (Category.assoc _ _ _).symm
      _ = (L.blowupMap ≫ p₁) ≫ s₁ := by rw [hn₁]
      _ = L.blowupMap ≫ p₂ ≫ s₂ := by rw [Category.assoc, hcomm]
      _ = (n₂ ≫ C₂.I.blowupMap) ≫ s₂ := by rw [hn₂, Category.assoc]
      _ = n₂ ≫ C₂.I.blowupMap ≫ s₂ := Category.assoc _ _ _
  -- the overlap is a closed subscheme of the fibre product, so the gluing is separated
  have hδ : IsClosedImmersion (pullback.lift n₁ n₂ hw) := by
    obtain ⟨δ, hδdef⟩ : ∃ d : L.blowup ⟶ pullback (C₁.I.blowupMap ≫ s₁)
        (C₂.I.blowupMap ≫ s₂), d = pullback.lift n₁ n₂ hw := ⟨_, rfl⟩
    rw [← hδdef]
    have hδ₁ : δ ≫ pullback.fst (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) = n₁ := by
      rw [hδdef]; exact pullback.lift_fst _ _ _
    have hδ₂ : δ ≫ pullback.snd (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) = n₂ := by
      rw [hδdef]; exact pullback.lift_snd _ _ _
    -- `δ` is a preimmersion: it is a closed immersion into the open locus over `n₁`
    have : IsPreimmersion δ := by
      rw [← partialSection_openι (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) n₁ δ hδ₁]
      infer_instance
    -- `δ` has closed range: it is universally closed, being universally closed over the
    -- separated comparison morphism to `X₁ ×_S X₂`
    have : IsProper L.blowupMap := L.isProper_blowupMap fun V ↦ hLft V le_top
    obtain ⟨θ, hθdef⟩ : ∃ t : pullback (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) ⟶
        pullback s₁ s₂, t = pullback.map (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) s₁ s₂
          C₁.I.blowupMap C₂.I.blowupMap (𝟙 S) (by simp) (by simp) := ⟨_, rfl⟩
    have : IsSeparated θ := by
      rw [hθdef]
      exact MorphismProperty.pullbackMap (P := @IsSeparated) inferInstance inferInstance rfl rfl
    have hθ : δ ≫ θ = L.blowupMap ≫ γ.imageι := by
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, hθdef, pullback.lift_fst, ← Category.assoc, hδ₁, hn₁,
          Category.assoc, hp₁def]
      · rw [Category.assoc, hθdef, pullback.lift_snd, ← Category.assoc, hδ₂, hn₂,
          Category.assoc, hp₂def]
    have : UniversallyClosed (δ ≫ θ) := by rw [hθ]; infer_instance
    have : UniversallyClosed δ := UniversallyClosed.of_comp_of_isSeparated δ θ
    refine IsClosedImmersion.of_isPreimmersion δ ?_
    rw [← Set.image_univ]
    exact δ.isClosedMap _ isClosed_univ
  exact ⟨{ B₁ := C₁, B₂ := C₂, W := pushout n₁ n₂
           w := pushout.desc (C₁.I.blowupMap ≫ s₁) (C₂.I.blowupMap ≫ s₂) hw
           k₁ := pushout.inl n₁ n₂, k₂ := pushout.inr n₁ n₂
           isOpenImmersion_k₁ := inferInstance, isOpenImmersion_k₂ := inferInstance
           k₁_w := pushout.inl_desc _ _ _, k₂_w := pushout.inr_desc _ _ _
           u₁ := u ≫ n₁, u₂ := u ≫ n₂
           u₁_blowupMap := hu₁, u₂_blowupMap := hu₂
           u_glue := by rw [Category.assoc, Category.assoc, pushout.condition]
           cover := range_pushout_inl_union_range_pushout_inr n₁ n₂
           isSeparated_w := IsSeparated.pushout_desc n₁ n₂ hw hδ
           locallyOfFiniteType_w := IsZariskiLocalAtSource.pushout_desc n₁ n₂ hw
             inferInstance inferInstance
           quasiCompact_w := QuasiCompact.pushout_desc n₁ n₂ hw }⟩

namespace CommonModification

variable {s₁ : X₁ ⟶ S} {s₂ : X₂ ⟶ S} {j₁ : U ⟶ X₁} {j₂ : U ⟶ X₂} [IsOpenImmersion j₁]
  [IsOpenImmersion j₂] (cm : CommonModification s₁ s₂ j₁ j₂)

instance isOpenImmersion_u₁ : IsOpenImmersion cm.u₁ :=
  isOpenImmersion_of_comp_of_isIso_restrict cm.u₁ cm.B₁.I.blowupMap j₁ cm.u₁_blowupMap
    cm.B₁.isIso_blowupMap_restrict

instance isOpenImmersion_u₂ : IsOpenImmersion cm.u₂ :=
  isOpenImmersion_of_comp_of_isIso_restrict cm.u₂ cm.B₂.I.blowupMap j₂ cm.u₂_blowupMap
    cm.B₂.isIso_blowupMap_restrict

/-- The open immersion `U ⟶ W` of the common open into the glued common modification,
through either modified model. -/
def j : U ⟶ cm.W := cm.u₁ ≫ cm.k₁

lemma u₁_k₁ : cm.u₁ ≫ cm.k₁ = cm.j := rfl

lemma u₂_k₂ : cm.u₂ ≫ cm.k₂ = cm.j := cm.u_glue.symm

instance : IsOpenImmersion cm.j := by
  rw [← u₁_k₁]
  infer_instance

@[reassoc]
lemma j_w : cm.j ≫ cm.w = j₁ ≫ s₁ := by
  rw [← u₁_k₁, Category.assoc, cm.k₁_w, ← Category.assoc, cm.u₁_blowupMap]

/-- The copy of `U` in the first modified model is the full inverse image of the copy of
`U` in the first model. -/
lemma range_u₁ : Set.range cm.u₁ = cm.B₁.I.blowupMap ⁻¹' Set.range j₁ :=
  range_eq_preimage_of_comp_of_isIso_restrict cm.u₁ cm.B₁.I.blowupMap j₁ cm.u₁_blowupMap
    cm.B₁.isIso_blowupMap_restrict

/-- The copy of `U` in the second modified model is the full inverse image of the copy of
`U` in the second model. -/
lemma range_u₂ : Set.range cm.u₂ = cm.B₂.I.blowupMap ⁻¹' Set.range j₂ :=
  range_eq_preimage_of_comp_of_isIso_restrict cm.u₂ cm.B₂.I.blowupMap j₂ cm.u₂_blowupMap
    cm.B₂.isIso_blowupMap_restrict

/-- **Density transport through the common modification** (blueprint:
`lemma:nagata-two-open-density-transport`): if `U` is dense in both Noetherian models,
then it is dense in the glued common modification. The `U`-admissible blow-ups preserve
the density of `U` (`IsAdmissible.dense_preimage_blowupMap`), and the two modified models
form an open cover of the glued scheme. -/
theorem dense_range_j [IsNoetherian X₁] [IsNoetherian X₂] (h₁ : Dense (Set.range j₁))
    (h₂ : Dense (Set.range j₂)) : Dense (Set.range cm.j) := by
  have hd₁ : Dense (Set.range cm.u₁) := by
    rw [cm.range_u₁]
    exact cm.B₁.dense_preimage_blowupMap h₁
  have hd₂ : Dense (Set.range cm.u₂) := by
    rw [cm.range_u₂]
    exact cm.B₂.dense_preimage_blowupMap h₂
  rw [dense_iff_inter_open]
  rintro W₀ hW₀ ⟨w₀, hw₀⟩
  have chartCase : ∀ {W' : Scheme.{u}} (k : W' ⟶ cm.W) (uu : U ⟶ W'),
      Dense (Set.range uu) → uu ≫ k = cm.j → w₀ ∈ Set.range k →
      (W₀ ∩ Set.range cm.j).Nonempty := by
    rintro W' k uu hdu hglue ⟨b₀, rfl⟩
    obtain ⟨-, hbW₀, y, rfl⟩ := dense_iff_inter_open.mp hdu (k ⁻¹' W₀)
      (hW₀.preimage k.continuous) ⟨b₀, hw₀⟩
    refine ⟨cm.j y, ?_, y, rfl⟩
    rwa [← hglue, Scheme.Hom.comp_apply]
  have hw₀cov : w₀ ∈ Set.range cm.k₁ ∪ Set.range cm.k₂ := by
    rw [cm.cover]
    trivial
  obtain hw₀k | hw₀k := hw₀cov
  · exact chartCase cm.k₁ cm.u₁ hd₁ cm.u₁_k₁ hw₀k
  · exact chartCase cm.k₂ cm.u₂ hd₂ cm.u₂_k₂ hw₀k

end CommonModification

end CommonModification

end AlgebraicGeometry
