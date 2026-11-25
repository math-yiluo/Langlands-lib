/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.AdmissibleBlowup
public import WeilConjectures.Blowup.GraphQuasiFinite
public import WeilConjectures.Blowup.PartialSectionExtensionReduction

/-!

# Extending a partial section after an admissible blow-up

This file proves **Conrad's Theorem 2.4** in the reduced form in which it is used on the
Conrad/Zariski's-Main-Theorem route to elimination of indeterminacy (Stacks Project Tag
081S), together with the special case recorded as Conrad's Remark 2.5.

Reference: Brian Conrad, *Deligne's notes on Nagata compactifications*, Theorem 2.4 and
Remark 2.5.

Conrad states his theorem over an auxiliary base `S`, for a morphism `Y ⟶ S` and a
rational `S`-map from `X` to `Y`; the first step of his proof replaces `Y` by `Y ×_S X`
and thereby reduces to the case `S = X`. Only that reduced form is stated here:

- `AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection`: let `X` be a qcqs
  scheme, `U ≤ V` quasi-compact opens of `X` with `U` dense, and `p : Y ⟶ X` a separated
  quasi-compact morphism locally of finite type with `Y` qcqs. A section `f` of `p` over
  `U` whose image is closed in `p⁻¹(V)` extends, after a `V`-admissible blow-up of `X`,
  to a section of `p` over an open `W` of the blow-up containing the preimage of `U`, and
  the graph of the extension is closed in `Y ×_X X'`
  (blueprint: `thm:nagata-conrad-elimination`, in the form reduced to the base `X`);
- `AlgebraicGeometry.exists_admissibleBlowup_extend_section`: **Conrad's Remark 2.5**, the
  case `V = U`. Here the closed-image hypothesis is automatic: `f` is then a section of
  the separated morphism `p ∣_ U`, hence a closed immersion
  (blueprint: `lemma:nagata-conrad-morphism-is-quasi-domination`).

The first statement is what
`AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap` (Tag 081S)
in `WeilConjectures.Compactification.EliminationOfIndeterminacy` is deduced from; with its
proof here,
that deduction and the Nagata compactification theorem's dependence on it are
unconditional.

## Structure of the proof

The mathematics is in the three files imported here, and the proof below is their
assembly:

1. if `p` is quasi-affine as a morphism, the statement is Conrad's Case 3,
   `AlgebraicGeometry.exists_isAdmissible_extend_of_isQuasiAffineHom_of_le`;
2. in general
   `AlgebraicGeometry.exists_isAdmissible_locallyQuasiFinite_image_graph` produces a
   `V`-admissible blow-up `q : X̃ ⟶ X` over which the scheme-theoretic image `F(U)‾` of the
   graph `F = (f, σ)` is quasi-finite, of finite type, separated and quasi-compact over
   `X̃`;
3. `AlgebraicGeometry.IsQuasiAffineHom.of_locallyQuasiFinite` (Zariski's Main Theorem)
   turns those four properties into quasi-affineness of `F(U)‾ ⟶ X̃` *as a morphism* —
   neither `X̃` nor `F(U)‾` is quasi-affine as a scheme;
4. `AlgebraicGeometry.exists_isAdmissible_extend_partialSection_of_blowup` base changes
   the whole problem along `q`, and
5. `AlgebraicGeometry.exists_isAdmissible_extend_partialSection_of_isClosedImmersion`
   replaces the base-changed target `Y ×_X X̃` by the closed subscheme `F(U)‾`, which by
   step 3 is quasi-affine over `X̃`, reducing to step 1.

The two orientations of the fibre product have to be reconciled: step 2 works in
`Y ×_X X̃ = pullback p q` and steps 4 and 5 in `X̃ ×_X Y = pullback q p`. The bridge is
`CategoryTheory.Limits.pullbackSymmetry`, and it is used only through the closed immersion
`F.imageι ≫ (pullbackSymmetry p q).hom`, so that no transport of scheme-theoretic images
along an isomorphism is needed.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **Conrad's Theorem 2.4, reduced to the base `X`** (blueprint:
`thm:nagata-conrad-elimination`, in the form reduced to the base `X`;
`def:nagata-conrad-quasi-domination`).

Conrad's Theorem 2.4 is stated for a rational map over an auxiliary base `S`; the first
step of his proof replaces `Y` by `Y ×_S X`, which is the reduction to the form stated
here. In the vocabulary of the blueprint the hypothesis says that `(U, f)` is a
quasi-domination of `V` over `Y`, and the conclusion that `(W, g)` is a
quasi-domination of the blow-up over `Y` extending `f`.

Elimination of indeterminacy (Stacks Project Tag 081S,
`AlgebraicGeometry.exists_admissibleBlowup_isOpenImmersion_strictTransformMap`) is
deduced from this statement.

Density of `U` is not used: neither Conrad's Case 3 nor the quasi-finiteness of the graph
needs it. The hypothesis is kept because it is part of the interface consumed
downstream. -/
theorem exists_admissibleBlowup_extend_partialSection
    [CompactSpace X] [QuasiSeparatedSpace X] {U V : X.Opens} (hUV : U ≤ V)
    (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (_hUdense : Dense (U : Set X))
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {p : Y ⟶ X}
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι)
    (hfc : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range f)) :
    ∃ (B : IsAdmissible X V) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  -- **Step 2**: a `V`-admissible blow-up over which the graph has quasi-finite image.
  obtain ⟨B₁, σ, -, hσ, hQF⟩ :=
    exists_isAdmissible_locallyQuasiFinite_image_graph hUV hU hV f hf hfc
  obtain ⟨F, hFfst, hFsnd⟩ :
      ∃ F : U.toScheme ⟶ pullback p B₁.I.blowupMap,
        F ≫ pullback.fst p B₁.I.blowupMap = f ∧
          F ≫ pullback.snd p B₁.I.blowupMap = σ :=
    ⟨pullback.lift f σ (by rw [hf, hσ]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨hqf, hft, hsep, hqc⟩ := hQF F hFfst hFsnd
  have : LocallyQuasiFinite (F.imageι ≫ pullback.snd p B₁.I.blowupMap) := hqf
  have : LocallyOfFiniteType (F.imageι ≫ pullback.snd p B₁.I.blowupMap) := hft
  have : IsSeparated (F.imageι ≫ pullback.snd p B₁.I.blowupMap) := hsep
  have : QuasiCompact (F.imageι ≫ pullback.snd p B₁.I.blowupMap) := hqc
  -- the section `σ` is the canonical isomorphism onto the preimage of `U`
  have hrange : Set.range σ ⊆ Set.range (B₁.I.blowupMap ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨u, rfl⟩
    change B₁.I.blowupMap (σ u) ∈ U
    rw [← Scheme.Hom.comp_apply, hσ]
    exact u.2
  set s : U.toScheme ⟶ (B₁.I.blowupMap ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.lift (B₁.I.blowupMap ⁻¹ᵁ U).ι σ hrange with hsdef
  have hsι : s ≫ (B₁.I.blowupMap ⁻¹ᵁ U).ι = σ := IsOpenImmersion.lift_fac _ _ _
  have hUVset : (U : Set X) ≤ (V : Set X) := fun _ hx ↦ hUV hx
  have : IsIso (B₁.I.blowupMap ∣_ U) :=
    B₁.I.isIso_blowupMap_restrict (B₁.disjoint_support.mono_left hUVset)
  have hsid : s ≫ (B₁.I.blowupMap ∣_ U) = 𝟙 U.toScheme := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hsι, hσ,
      Category.id_comp]
  have : IsIso s := by
    have hs : s = inv (B₁.I.blowupMap ∣_ U) := by
      rw [← Category.comp_id s, ← IsIso.hom_inv_id (B₁.I.blowupMap ∣_ U), ← Category.assoc,
        hsid, Category.id_comp]
    rw [hs]
    infer_instance
  -- **The interface seam**: the two orientations of the fibre product `Y ×[X] X̃`.
  have hτfst : (pullbackSymmetry p B₁.I.blowupMap).hom ≫ pullback.fst B₁.I.blowupMap p
      = pullback.snd p B₁.I.blowupMap := pullbackSymmetry_hom_comp_fst p B₁.I.blowupMap
  have hτsnd : (pullbackSymmetry p B₁.I.blowupMap).hom ≫ pullback.snd B₁.I.blowupMap p
      = pullback.fst p B₁.I.blowupMap := pullbackSymmetry_hom_comp_snd p B₁.I.blowupMap
  have hbcs : s ≫ baseChangeSection f hf B₁
      = F ≫ (pullbackSymmetry p B₁.I.blowupMap).hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, baseChangeSection_comp_fst, hsι, Category.assoc, hτfst, hFsnd]
    · rw [Category.assoc, baseChangeSection_comp_snd, ← Category.assoc, hsid, Category.id_comp,
        Category.assoc, hτsnd, hFfst]
  -- **Step 3**: Zariski's Main Theorem makes the image quasi-affine over the blow-up.
  have : IsQuasiAffineHom (F.imageι ≫ pullback.snd p B₁.I.blowupMap) :=
    IsQuasiAffineHom.of_locallyQuasiFinite _
  set i : F.image ⟶ pullback B₁.I.blowupMap p :=
    F.imageι ≫ (pullbackSymmetry p B₁.I.blowupMap).hom with hidef
  have : IsClosedImmersion i := by rw [hidef]; infer_instance
  have hi : i ≫ pullback.fst B₁.I.blowupMap p
      = F.imageι ≫ pullback.snd p B₁.I.blowupMap := by
    rw [hidef, Category.assoc, hτfst]
  set f' : (B₁.I.blowupMap ⁻¹ᵁ U).toScheme ⟶ F.image := inv s ≫ F.toImage with hf'def
  have hf'i : f' ≫ i = baseChangeSection f hf B₁ := by
    simp only [hf'def, hidef, Category.assoc, Scheme.Hom.toImage_imageι_assoc, ← hbcs,
      IsIso.inv_hom_id_assoc]
  -- the hypotheses of Case 3 over the blow-up
  have : QuasiCompact B₁.I.blowupMap := B₁.quasiCompact_blowupMap
  have : CompactSpace B₁.I.blowup :=
    QuasiCompact.compactSpace_of_compactSpace B₁.I.blowupMap
  have : IsSeparated B₁.I.blowupMap := B₁.isProper_blowupMap.toIsSeparated
  have : QuasiSeparatedSpace B₁.I.blowup :=
    quasiSeparatedSpace_of_quasiSeparated B₁.I.blowupMap
  have : CompactSpace F.image :=
    QuasiCompact.compactSpace_of_compactSpace (F.imageι ≫ pullback.snd p B₁.I.blowupMap)
  have : QuasiSeparatedSpace F.image :=
    quasiSeparatedSpace_of_quasiSeparated (F.imageι ≫ pullback.snd p B₁.I.blowupMap)
  have hf'p : f' ≫ (F.imageι ≫ pullback.snd p B₁.I.blowupMap) = (B₁.I.blowupMap ⁻¹ᵁ U).ι := by
    rw [← hi, ← Category.assoc, hf'i, baseChangeSection_comp_fst]
  have hf'c : IsClosed (((F.imageι ≫ pullback.snd p B₁.I.blowupMap)
      ⁻¹ᵁ (B₁.I.blowupMap ⁻¹ᵁ V)).ι ⁻¹' Set.range f') := by
    have hbc := B₁.isClosed_preimage_range_baseChangeSection f hf hfc
    set O : (pullback B₁.I.blowupMap p : Scheme.{u}).Opens :=
      pullback.fst B₁.I.blowupMap p ⁻¹ᵁ (B₁.I.blowupMap ⁻¹ᵁ V) with hOdef
    have hpre : (F.imageι ≫ pullback.snd p B₁.I.blowupMap) ⁻¹ᵁ (B₁.I.blowupMap ⁻¹ᵁ V)
        = i ⁻¹ᵁ O := by
      rw [hOdef, ← hi, Scheme.Hom.comp_preimage]
    have hrng : ⇑i ⁻¹' Set.range (baseChangeSection f hf B₁) = Set.range f' := by
      rw [← hf'i]
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
      exact Set.preimage_image_eq _ i.isClosedEmbedding.injective
    have hset : ⇑(i ⁻¹ᵁ O).ι ⁻¹' Set.range f'
        = ⇑(i ∣_ O) ⁻¹' (⇑O.ι ⁻¹' Set.range (baseChangeSection f hf B₁)) := by
      have h := congrArg
        (fun t : (i ⁻¹ᵁ O).toScheme ⟶ (pullback B₁.I.blowupMap p : Scheme.{u}) =>
          ⇑t ⁻¹' Set.range (baseChangeSection f hf B₁)) (morphismRestrict_ι i O).symm
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at h
      rw [← hrng]
      exact h
    rw [hpre, hset]
    exact hbc.preimage (i ∣_ O).continuous
  -- **Steps 4 and 5**: base change along the blow-up, then replace the target by the image.
  refine exists_isAdmissible_extend_partialSection_of_blowup f hf B₁ ?_
  rw [← hf'i]
  -- **Step 1**: Case 3, applied to the quasi-affine morphism `F(U)‾ ⟶ X̃`.
  exact exists_isAdmissible_extend_partialSection_of_isClosedImmersion i hi f'
    (exists_isAdmissible_extend_of_isQuasiAffineHom_of_le
      (B₁.preimage_blowupMap_mono hUV) (B₁.isCompact_coe_preimage_blowupMap hU)
      (B₁.isCompact_coe_preimage_blowupMap hV) f' hf'p hf'c)

/-- Blueprint `corollary-extension-proper-target--1`, section form.

**Conrad's Remark 2.5**: the case `V = U` of
`AlgebraicGeometry.exists_admissibleBlowup_extend_partialSection` (blueprint:
`thm:nagata-conrad-elimination` with `V = U`, together with
`lemma:nagata-conrad-morphism-is-quasi-domination`). Combined with
`AlgebraicGeometry.QuasiDomination.U_eq_top` it yields the extension to a proper target
`AlgebraicGeometry.exists_admissibleBlowup_extend_of_isProper`.

No closedness hypothesis is needed: over `U` the morphism `f` is a section of the
separated morphism `p ∣_ U`, hence a closed immersion, so its image is closed in
`p⁻¹(U)`. -/
theorem exists_admissibleBlowup_extend_section
    [CompactSpace X] [QuasiSeparatedSpace X] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hUdense : Dense (U : Set X))
    {Y : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y] {p : Y ⟶ X}
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (f : U.toScheme ⟶ Y) (hf : f ≫ p = U.ι) :
    ∃ (B : IsAdmissible X U) (W : B.I.blowup.Opens) (hUW : B.I.blowupMap ⁻¹ᵁ U ≤ W)
      (g : W.toScheme ⟶ Y) (hg : g ≫ p = W.ι ≫ B.I.blowupMap),
      B.I.blowup.homOfLE hUW ≫ g = (B.I.blowupMap ∣_ U) ≫ f ∧
        IsClosed (Set.range (pullback.lift g W.ι hg)) := by
  refine exists_admissibleBlowup_extend_partialSection le_rfl hU hU hUdense f hf ?_
  -- `f` factors through the open `p ⁻¹ᵁ U`, since `p ∘ f` is the inclusion of `U`
  have hrange : Set.range f ⊆ Set.range (p ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨u, rfl⟩
    change p (f u) ∈ U
    rw [← Scheme.Hom.comp_apply, hf]
    exact u.2
  set f₀ : U.toScheme ⟶ (p ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (p ⁻¹ᵁ U).ι f hrange
  have hf₀ : f₀ ≫ (p ⁻¹ᵁ U).ι = f := IsOpenImmersion.lift_fac _ _ _
  -- `f₀` is a section of the separated morphism `p ∣_ U`, hence a closed immersion
  have hsec : f₀ ≫ (p ∣_ U) = 𝟙 U.toScheme := by
    rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hf₀, hf,
      Category.id_comp]
  have : IsClosedImmersion (f₀ ≫ (p ∣_ U)) := by rw [hsec]; infer_instance
  have : IsClosedImmersion f₀ := IsClosedImmersion.of_comp f₀ (p ∣_ U)
  have hcl : IsClosed (Set.range f₀) := f₀.isClosedEmbedding.isClosed_range
  have himg : (p ⁻¹ᵁ U).ι ⁻¹' Set.range f = Set.range f₀ := by
    rw [← hf₀, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.preimage_image_eq _ (p ⁻¹ᵁ U).ι.isOpenEmbedding.injective]
  rw [himg]
  exact hcl

end AlgebraicGeometry
