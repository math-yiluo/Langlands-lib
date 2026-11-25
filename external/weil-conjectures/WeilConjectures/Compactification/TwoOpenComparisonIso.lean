/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.TwoOpenComparison

/-!

# Scheme-level statements about the two-open comparison space

This file complements `WeilConjectures.Compactification.TwoOpenComparison` with the
scheme-level forms of the statements of the blueprint subsections
`proposition-compactifying-union-two-opens--1`, which the
main chain of the two-open compactification theorem only uses in topological form.

* `AlgebraicGeometry.TwoOpenSide.boundaryLoci`: all clauses of
  `lemma-nagata-boundary-loci`.
* `AlgebraicGeometry.TwoOpenSide.pullbackIsoComparisonFstPreimage`,
  `AlgebraicGeometry.TwoOpenSide.isPullback_comparisonFst_restrict` and their analogues
  for the second projection: over `Vᵢ` the comparison space is `V₁ ×_U V₂`, and
  `pᵢ⁻¹(Vᵢ) ⟶ Vᵢ` is the base change of `ψⱼ` along `ψᵢ`
  (`lemma-nagata-key-boundary-disjointness`, part (2)).
* `AlgebraicGeometry.TwoOpenSide.comparisonSpaceAdmissibleBlowupIso`: after a
  `V₁`-admissible blow-up of `X₁`, the new comparison space is the strict transform of
  the old one (`lemma-nagata-key-boundary-disjointness`, part (3)).
* `AlgebraicGeometry.exists_admissibleBlowup_isIso_comparisonFst_near_forbiddenBoundary`:
  after the isomorphism-near-closure blow-up, the new first projection is an isomorphism
  over an open neighbourhood of the forbidden boundary `Z̄₁,₂`, and the comparison
  boundary lands in the self boundary of the second side (parts (3) and (4)).
* `AlgebraicGeometry.exists_prepared_keyDisjoint_isIso_near_twoOpenSide`: the full
  statement of `lemma-nagata-key-boundary-disjointness`.

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {U S : Scheme.{u}} {u : U ⟶ S}

namespace TwoOpenSide

section BoundaryLoci

variable {O : U.Opens} (σ : TwoOpenSide u O)

/-- **The four boundary loci** (blueprint: `proposition-compactifying-union-two-opens--1`). For a
side `σ` over `O` and the other open `O'` with `O ∪ O' = U`, write `Z = U ∖ O'` and `Z' = U ∖ O`.
Then `Z` is closed in `U` and contained in `O`; the loci `ψ⁻¹(Z)` and `ψ⁻¹(Z')` are
closed in `V`, i.e. their closures in `X` (the self and the forbidden boundary) meet `V`
exactly in them; they are disjoint; and `ψ` is an isomorphism over an open neighbourhood
of `Z`. -/
theorem boundaryLoci {O' : U.Opens} (hcov : O ⊔ O' = ⊤) :
    IsClosed ((O' : Set U)ᶜ) ∧ (O' : Set U)ᶜ ⊆ (O : Set U) ∧
      IsClosed (σ.ψ ⁻¹' (O' : Set U)ᶜ) ∧ IsClosed (σ.ψ ⁻¹' (O : Set U)ᶜ) ∧
      σ.selfBoundary O' ∩ (σ.V : Set σ.X) = σ.V.ι '' (σ.ψ ⁻¹' (O' : Set U)ᶜ) ∧
      σ.forbiddenBoundary ∩ (σ.V : Set σ.X) = σ.V.ι '' (σ.ψ ⁻¹' (O : Set U)ᶜ) ∧
      Disjoint (σ.ψ ⁻¹' (O' : Set U)ᶜ) (σ.ψ ⁻¹' (O : Set U)ᶜ) ∧
      ∃ W : U.Opens, (O' : Set U)ᶜ ⊆ (W : Set U) ∧ IsIso (σ.ψ ∣_ W) := by
  have huniv : (O : Set U) ∪ (O' : Set U) = Set.univ := by
    have h := congrArg (fun W : U.Opens ↦ (W : Set U)) hcov
    simpa using h
  have hsub : (O' : Set U)ᶜ ⊆ (O : Set U) := by
    intro x hx
    rcases Set.eq_univ_iff_forall.mp huniv x with h | h
    · exact h
    · exact absurd h hx
  refine ⟨O'.isOpen.isClosed_compl, hsub,
    O'.isOpen.isClosed_compl.preimage σ.ψ.continuous,
    O.isOpen.isClosed_compl.preimage σ.ψ.continuous,
    σ.closure_image_preimage_inter O'.isOpen.isClosed_compl,
    σ.closure_image_preimage_inter O.isOpen.isClosed_compl, ?_, O, hsub, inferInstance⟩
  refine Disjoint.preimage _ ?_
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.compl_union, Set.union_comm, huniv,
    Set.compl_univ]

end BoundaryLoci

variable {O₁ O₂ : U.Opens} (σ₁ : TwoOpenSide u O₁) (σ₂ : TwoOpenSide u O₂)

section ComparisonOverV

/-! ### The comparison space over `V₁` and over `V₂` -/

lemma range_comparisonMap_subset_snd :
    Set.range ⇑(comparisonMap σ₁ σ₂) ⊆
      Set.range ⇑(pullback.snd σ₁.s σ₂.s ⁻¹ᵁ σ₂.V).ι := by
  rw [Scheme.Opens.range_ι]
  rintro - ⟨w, rfl⟩
  have h : pullback.snd σ₁.s σ₂.s (comparisonMap σ₁ σ₂ w) ∈ (σ₂.V : Set σ₂.X) := by
    rw [← Scheme.Hom.comp_apply, comparisonMap_snd, Scheme.Hom.comp_apply,
      ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  exact h

/-- The comparison morphism, viewed as a morphism into the locus of `X₁ ×_S X₂` over the
proper-extension open `V₂`. -/
def comparisonMapRestrictSnd :
    pullback σ₁.ψ σ₂.ψ ⟶ (pullback.snd σ₁.s σ₂.s ⁻¹ᵁ σ₂.V).toScheme :=
  IsOpenImmersion.lift (pullback.snd σ₁.s σ₂.s ⁻¹ᵁ σ₂.V).ι (comparisonMap σ₁ σ₂)
    (range_comparisonMap_subset_snd σ₁ σ₂)

@[reassoc (attr := simp)]
lemma comparisonMapRestrictSnd_ι :
    comparisonMapRestrictSnd σ₁ σ₂ ≫ (pullback.snd σ₁.s σ₂.s ⁻¹ᵁ σ₂.V).ι =
      comparisonMap σ₁ σ₂ :=
  IsOpenImmersion.lift_fac _ _ _

lemma comparisonMapRestrictSnd_snd :
    comparisonMapRestrictSnd σ₁ σ₂ ≫ (pullback.snd σ₁.s σ₂.s ∣_ σ₂.V) =
      pullback.snd σ₁.ψ σ₂.ψ := by
  rw [← cancel_mono σ₂.V.ι, Category.assoc, morphismRestrict_ι,
    comparisonMapRestrictSnd_ι_assoc, comparisonMap_snd]

/-- The comparison morphism is proper over `V₂`, since `V₁ ×_U V₂ ⟶ V₂` is a base change
of the proper morphism `ψ₁` and `X₁ ×_S X₂ ⟶ X₂` is separated. -/
instance isProper_comparisonMapRestrictSnd : IsProper (comparisonMapRestrictSnd σ₁ σ₂) := by
  have : IsProper (comparisonMapRestrictSnd σ₁ σ₂ ≫ (pullback.snd σ₁.s σ₂.s ∣_ σ₂.V)) := by
    rw [comparisonMapRestrictSnd_snd]
    infer_instance
  have : IsProper (pullback.snd σ₁.s σ₂.s) := inferInstance
  exact IsProper.of_comp _ (pullback.snd σ₁.s σ₂.s ∣_ σ₂.V)

lemma preimage_range_comparisonMap_snd :
    ⇑(pullback.snd σ₁.s σ₂.s ⁻¹ᵁ σ₂.V).ι ⁻¹' Set.range ⇑(comparisonMap σ₁ σ₂) =
      Set.range ⇑(comparisonMapRestrictSnd σ₁ σ₂) := by
  ext x
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨w, (pullback.snd σ₁.s σ₂.s ⁻¹ᵁ σ₂.V).ι.isOpenEmbedding.injective
      (by rw [← Scheme.Hom.comp_apply, comparisonMapRestrictSnd_ι, hw])⟩
  · rintro ⟨w, rfl⟩
    exact ⟨w, by rw [← Scheme.Hom.comp_apply, comparisonMapRestrictSnd_ι]⟩

variable [IsNoetherian S]

/-- Over the proper-extension open `V₂`, the comparison space is the image of
`V₁ ×_U V₂` (the analogue of `TwoOpenSide.range_toImage_comparisonMap` for the second
projection). -/
theorem range_toImage_comparisonMap_snd :
    Set.range ⇑(comparisonMap σ₁ σ₂).toImage =
      ⇑(comparisonSnd σ₁ σ₂) ⁻¹' (σ₂.V : Set σ₂.X) := by
  apply subset_antisymm
  · rintro - ⟨w, rfl⟩
    refine Set.mem_preimage.mpr ?_
    rw [comparisonSnd_toImage_apply, ← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  · have hsub := (comparisonMap σ₁ σ₂).preimage_subset_range_toImage_of_isClosed
      (W := pullback.snd σ₁.s σ₂.s ⁻¹ᵁ σ₂.V) (by
        rw [preimage_range_comparisonMap_snd]
        have h := (comparisonMapRestrictSnd σ₁ σ₂).isClosedMap _ isClosed_univ
        rwa [Set.image_univ] at h)
    intro z hz
    refine hsub ?_
    have h : pullback.snd σ₁.s σ₂.s ((comparisonMap σ₁ σ₂).imageι z) ∈
        (σ₂.V : Set σ₂.X) := by
      rw [← Scheme.Hom.comp_apply, ← comparisonSnd_eq]
      exact hz
    exact h

/-- The canonical isomorphism `V₁ ×_U V₂ ≅ p₁⁻¹(V₁)` (blueprint:
`proposition-compactifying-union-two-opens--1`, part (2)): the comparison morphism is a
quasi-compact immersion, so it is an open immersion into its scheme-theoretic image, with
range `p₁⁻¹(V₁)`. -/
def pullbackIsoComparisonFstPreimage :
    pullback σ₁.ψ σ₂.ψ ≅ (comparisonFst σ₁ σ₂ ⁻¹ᵁ σ₁.V).toScheme :=
  IsOpenImmersion.isoOfRangeEq (comparisonMap σ₁ σ₂).toImage
    (comparisonFst σ₁ σ₂ ⁻¹ᵁ σ₁.V).ι
    (by rw [Scheme.Opens.range_ι, range_toImage_comparisonMap]; rfl)

/-- The canonical isomorphism `V₁ ×_U V₂ ≅ p₂⁻¹(V₂)` (blueprint:
`proposition-compactifying-union-two-opens--1`, part (2)). -/
def pullbackIsoComparisonSndPreimage :
    pullback σ₁.ψ σ₂.ψ ≅ (comparisonSnd σ₁ σ₂ ⁻¹ᵁ σ₂.V).toScheme :=
  IsOpenImmersion.isoOfRangeEq (comparisonMap σ₁ σ₂).toImage
    (comparisonSnd σ₁ σ₂ ⁻¹ᵁ σ₂.V).ι
    (by rw [Scheme.Opens.range_ι, range_toImage_comparisonMap_snd]; rfl)

@[reassoc (attr := simp)]
lemma pullbackIsoComparisonFstPreimage_hom_ι :
    (pullbackIsoComparisonFstPreimage σ₁ σ₂).hom ≫ (comparisonFst σ₁ σ₂ ⁻¹ᵁ σ₁.V).ι =
      (comparisonMap σ₁ σ₂).toImage :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
lemma pullbackIsoComparisonSndPreimage_hom_ι :
    (pullbackIsoComparisonSndPreimage σ₁ σ₂).hom ≫ (comparisonSnd σ₁ σ₂ ⁻¹ᵁ σ₂.V).ι =
      (comparisonMap σ₁ σ₂).toImage :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Under `V₁ ×_U V₂ ≅ p₁⁻¹(V₁)`, the restriction of `p₁` is the first projection. -/
@[reassoc (attr := simp)]
lemma pullbackIsoComparisonFstPreimage_hom_comparisonFst :
    (pullbackIsoComparisonFstPreimage σ₁ σ₂).hom ≫ (comparisonFst σ₁ σ₂ ∣_ σ₁.V) =
      pullback.fst σ₁.ψ σ₂.ψ := by
  rw [← cancel_mono σ₁.V.ι, Category.assoc, morphismRestrict_ι,
    pullbackIsoComparisonFstPreimage_hom_ι_assoc, toImage_comparisonFst]

/-- Under `V₁ ×_U V₂ ≅ p₁⁻¹(V₁)`, the second projection `p₂` is the second projection
followed by the inclusion of `V₂`. -/
@[reassoc (attr := simp)]
lemma pullbackIsoComparisonFstPreimage_hom_comparisonSnd :
    (pullbackIsoComparisonFstPreimage σ₁ σ₂).hom ≫ (comparisonFst σ₁ σ₂ ⁻¹ᵁ σ₁.V).ι ≫
      comparisonSnd σ₁ σ₂ = pullback.snd σ₁.ψ σ₂.ψ ≫ σ₂.V.ι := by
  rw [pullbackIsoComparisonFstPreimage_hom_ι_assoc, toImage_comparisonSnd]

/-- Under `V₁ ×_U V₂ ≅ p₂⁻¹(V₂)`, the restriction of `p₂` is the second projection. -/
@[reassoc (attr := simp)]
lemma pullbackIsoComparisonSndPreimage_hom_comparisonSnd :
    (pullbackIsoComparisonSndPreimage σ₁ σ₂).hom ≫ (comparisonSnd σ₁ σ₂ ∣_ σ₂.V) =
      pullback.snd σ₁.ψ σ₂.ψ := by
  rw [← cancel_mono σ₂.V.ι, Category.assoc, morphismRestrict_ι,
    pullbackIsoComparisonSndPreimage_hom_ι_assoc, toImage_comparisonSnd]

/-- Under `V₁ ×_U V₂ ≅ p₂⁻¹(V₂)`, the first projection `p₁` is the first projection
followed by the inclusion of `V₁`. -/
@[reassoc (attr := simp)]
lemma pullbackIsoComparisonSndPreimage_hom_comparisonFst :
    (pullbackIsoComparisonSndPreimage σ₁ σ₂).hom ≫ (comparisonSnd σ₁ σ₂ ⁻¹ᵁ σ₂.V).ι ≫
      comparisonFst σ₁ σ₂ = pullback.fst σ₁.ψ σ₂.ψ ≫ σ₁.V.ι := by
  rw [pullbackIsoComparisonSndPreimage_hom_ι_assoc, toImage_comparisonFst]

/-- **`p₁⁻¹(V₁) ⟶ V₁` is the base change of `ψ₂` along `ψ₁`** (blueprint:
`proposition-compactifying-union-two-opens--1`, part (2), `i = 1`). The square
```
p₁⁻¹(V₁) --> V₂
   |          | ψ₂
   v          v
   V₁ -ψ₁---> U
```
is cartesian, the top arrow being the second projection under
`TwoOpenSide.pullbackIsoComparisonFstPreimage`. -/
theorem isPullback_comparisonFst_restrict :
    IsPullback (comparisonFst σ₁ σ₂ ∣_ σ₁.V)
      ((pullbackIsoComparisonFstPreimage σ₁ σ₂).inv ≫ pullback.snd σ₁.ψ σ₂.ψ)
      σ₁.ψ σ₂.ψ := by
  have hfst : (pullbackIsoComparisonFstPreimage σ₁ σ₂).inv ≫ pullback.fst σ₁.ψ σ₂.ψ =
      comparisonFst σ₁ σ₂ ∣_ σ₁.V := by
    rw [Iso.inv_comp_eq, pullbackIsoComparisonFstPreimage_hom_comparisonFst]
  refine IsPullback.of_iso_pullback ⟨?_⟩ (pullbackIsoComparisonFstPreimage σ₁ σ₂).symm
    hfst rfl
  rw [← hfst, Category.assoc, Category.assoc, pullback.condition]

/-- **`p₂⁻¹(V₂) ⟶ V₂` is the base change of `ψ₁` along `ψ₂`** (blueprint:
`proposition-compactifying-union-two-opens--1`, part (2), `i = 2`). -/
theorem isPullback_comparisonSnd_restrict :
    IsPullback (comparisonSnd σ₁ σ₂ ∣_ σ₂.V)
      ((pullbackIsoComparisonSndPreimage σ₁ σ₂).inv ≫ pullback.fst σ₁.ψ σ₂.ψ)
      σ₂.ψ σ₁.ψ := by
  have hsnd : (pullbackIsoComparisonSndPreimage σ₁ σ₂).inv ≫ pullback.snd σ₁.ψ σ₂.ψ =
      comparisonSnd σ₁ σ₂ ∣_ σ₂.V := by
    rw [Iso.inv_comp_eq, pullbackIsoComparisonSndPreimage_hom_comparisonSnd]
  refine IsPullback.flip (IsPullback.of_iso_pullback ⟨?_⟩
    (pullbackIsoComparisonSndPreimage σ₁ σ₂).symm rfl hsnd)
  rw [← hsnd, Category.assoc, Category.assoc, pullback.condition]

end ComparisonOverV

section Improved

/-! ### The improved comparison space is the strict transform -/

variable [IsNoetherian S] (B : IsAdmissible σ₁.X σ₁.V)

instance isIso_blowupPullbackMap : IsIso (blowupPullbackMap σ₁ σ₂ B) := by
  have : IsIso (B.I.blowupMap ∣_ σ₁.V) := B.isIso_blowupMap_restrict
  rw [blowupPullbackMap]
  infer_instance

/-- The inclusion of the open locus over the preserved open into the base change of the
comparison space along the blow-up is quasi-compact. -/
lemma quasiCompact_strictTransformOpen_comparisonFst_ι :
    QuasiCompact (strictTransformOpen (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen).ι := by
  have := σ₁.isNoetherian_X
  have := isProper_comparisonFst σ₁ σ₂
  have := B.isProper_blowupMap
  have hX' : IsNoetherian B.I.blowup := (σ₁.admissibleBlowup B).isNoetherian_X
  have : IsLocallyNoetherian (pullback (comparisonFst σ₁ σ₂) B.I.blowupMap) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (comparisonFst σ₁ σ₂) B.I.blowupMap)
  have : CompactSpace ↥(pullback (comparisonFst σ₁ σ₂) B.I.blowupMap) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd (comparisonFst σ₁ σ₂) B.I.blowupMap)
  have : IsNoetherian (pullback (comparisonFst σ₁ σ₂) B.I.blowupMap) := ⟨⟩
  have : QuasiSeparatedSpace ↥(pullback (comparisonFst σ₁ σ₂) B.I.blowupMap) :=
    ⟨fun _ _ _ _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  exact quasiCompact_strictTransformOpen_ι_of_isCompact _ _ _
    (TopologicalSpace.NoetherianSpace.isCompact _)

/-- The factorization of the improved comparison morphism through the strict transform
of the old comparison space is scheme-theoretically dominant: over the preserved open the
blow-up is an isomorphism, so the open locus of the strict transform is the part of the
old comparison space over the preserved open, in which `V₁ ×_U V₂` is
scheme-theoretically dense. -/
instance isSchemeTheoreticallyDominant_improvedToStrictTransform :
    IsSchemeTheoreticallyDominant (improvedToStrictTransform σ₁ σ₂ B) := by
  have := quasiCompact_strictTransformOpen_comparisonFst_ι σ₁ σ₂ B
  have : IsIso (B.I.blowupMap ∣_ B.preservedOpen) :=
    B.I.isIso_blowupMap_restrict_support_compl
  -- the canonical morphism `V₁ ×_U V₂ ⟶ X₁₂` lands over the preserved open
  have hrange : Set.range ⇑(comparisonMap σ₁ σ₂).toImage ⊆
      Set.range ⇑(comparisonFst σ₁ σ₂ ⁻¹ᵁ B.preservedOpen).ι := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨w, rfl⟩
    change comparisonFst σ₁ σ₂ _ ∈ (B.preservedOpen : Set σ₁.X)
    rw [comparisonFst_toImage_apply]
    refine B.le_preservedOpen ?_
    change _ ∈ (σ₁.V : Set σ₁.X)
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  have ht : IsOpenImmersion.lift (comparisonFst σ₁ σ₂ ⁻¹ᵁ B.preservedOpen).ι
      (comparisonMap σ₁ σ₂).toImage hrange ≫ (comparisonFst σ₁ σ₂ ⁻¹ᵁ B.preservedOpen).ι =
      (comparisonMap σ₁ σ₂).toImage := IsOpenImmersion.lift_fac _ _ _
  have hsq : IsPullback (𝟙 _) (IsOpenImmersion.lift
      (comparisonFst σ₁ σ₂ ⁻¹ᵁ B.preservedOpen).ι (comparisonMap σ₁ σ₂).toImage hrange)
      (comparisonMap σ₁ σ₂).toImage (comparisonFst σ₁ σ₂ ⁻¹ᵁ B.preservedOpen).ι :=
    IsPullback.of_horiz_isIso_mono ⟨by rw [Category.id_comp, ht]⟩
  have : IsSchemeTheoreticallyDominant (IsOpenImmersion.lift
      (comparisonFst σ₁ σ₂ ⁻¹ᵁ B.preservedOpen).ι (comparisonMap σ₁ σ₂).toImage hrange) :=
    .of_isPullback hsq
  -- the lift into the open locus is that morphism up to isomorphisms
  have hk : Set.range (improvedToPullback σ₁ σ₂ B ≫
      pullback.fst (comparisonFst σ₁ σ₂) B.I.blowupMap ≫ comparisonFst σ₁ σ₂) ⊆
      (B.preservedOpen : Set σ₁.X) := by
    rw [← Category.assoc, improvedToPullback_fst, Category.assoc, toImage_comparisonFst]
    rintro - ⟨w, rfl⟩
    refine B.le_preservedOpen ?_
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    change _ ∈ (σ₁.V : Set σ₁.X)
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  have hlift : strictTransformOpenLift (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen
      (improvedToPullback σ₁ σ₂ B) hk ≫
        (strictTransformOpenIso (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen).hom =
      blowupPullbackMap σ₁ σ₂ B ≫ IsOpenImmersion.lift
        (comparisonFst σ₁ σ₂ ⁻¹ᵁ B.preservedOpen).ι (comparisonMap σ₁ σ₂).toImage hrange := by
    rw [← cancel_mono (comparisonFst σ₁ σ₂ ⁻¹ᵁ B.preservedOpen).ι]
    simp only [Category.assoc]
    rw [strictTransformOpenIso_hom_ι, strictTransformOpenLift_ι_assoc, improvedToPullback_fst,
      ht]
  have : IsSchemeTheoreticallyDominant (strictTransformOpenLift (comparisonFst σ₁ σ₂)
      B.I.blowupMap B.preservedOpen (improvedToPullback σ₁ σ₂ B) hk) := by
    rw [(Iso.eq_comp_inv _).mpr hlift]
    infer_instance
  unfold improvedToStrictTransform
  infer_instance

lemma ker_comparisonMap_admissibleBlowup :
    (strictTransformComparisonι σ₁ σ₂ B).ker =
      (comparisonMap (σ₁.admissibleBlowup B) σ₂).imageι.ker := by
  have h : (comparisonMap (σ₁.admissibleBlowup B) σ₂).imageι.ker =
      (comparisonMap (σ₁.admissibleBlowup B) σ₂).ker :=
    Scheme.IdealSheafData.ker_subschemeι _
  rw [h, ← improvedToStrictTransform_ι, Scheme.Hom.ker_comp_of_isSchemeTheoreticallyDominant]

/-- **The improved comparison space is the strict transform of the old one** (blueprint:
`proposition-compactifying-union-two-opens--1`, part (3); Stacks Project Tag 0F3Y). After a
`V₁`-admissible blow-up `π : X₁' ⟶ X₁`, the comparison space formed with `X₁'` is
canonically isomorphic, as a closed subscheme of `X₁' ×_S X₂`, to the strict transform of
the comparison space `X₁₂` along `π`. -/
def comparisonSpaceAdmissibleBlowupIso :
    comparisonSpace (σ₁.admissibleBlowup B) σ₂ ≅
      strictTransform (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen :=
  have := IsClosedImmersion.isIso_lift _ _ (ker_comparisonMap_admissibleBlowup σ₁ σ₂ B)
  asIso (IsClosedImmersion.lift (strictTransformComparisonι σ₁ σ₂ B)
    (comparisonMap (σ₁.admissibleBlowup B) σ₂).imageι
    (ker_comparisonMap_admissibleBlowup σ₁ σ₂ B).le)

@[reassoc (attr := simp)]
lemma comparisonSpaceAdmissibleBlowupIso_hom_ι :
    (comparisonSpaceAdmissibleBlowupIso σ₁ σ₂ B).hom ≫ strictTransformComparisonι σ₁ σ₂ B =
      (comparisonMap (σ₁.admissibleBlowup B) σ₂).imageι :=
  IsClosedImmersion.lift_fac _ _ _

/-- Under the identification with the strict transform, the new first projection is the
strict transform of the old one. -/
@[reassoc (attr := simp)]
lemma comparisonSpaceAdmissibleBlowupIso_hom_strictTransformMap :
    (comparisonSpaceAdmissibleBlowupIso σ₁ σ₂ B).hom ≫
        strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen =
      comparisonFst (σ₁.admissibleBlowup B) σ₂ := by
  rw [← strictTransformComparisonι_fst, comparisonSpaceAdmissibleBlowupIso_hom_ι_assoc]
  rfl

/-- Under the identification with the strict transform, the new second projection is the
projection to the old comparison space followed by the old second projection. -/
@[reassoc (attr := simp)]
lemma comparisonSpaceAdmissibleBlowupIso_hom_comparisonSnd :
    (comparisonSpaceAdmissibleBlowupIso σ₁ σ₂ B).hom ≫
        strictTransformToSource (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen ≫
          comparisonSnd σ₁ σ₂ =
      comparisonSnd (σ₁.admissibleBlowup B) σ₂ := by
  have h : strictTransformToSource (comparisonFst σ₁ σ₂) B.I.blowupMap B.preservedOpen ≫
      comparisonSnd σ₁ σ₂ = strictTransformComparisonι σ₁ σ₂ B ≫
        pullback.snd (B.I.blowupMap ≫ σ₁.s) σ₂.s := by
    rw [strictTransformComparisonι, Category.assoc, blowupComparison_snd,
      strictTransformToSource, Category.assoc]
  rw [h, comparisonSpaceAdmissibleBlowupIso_hom_ι_assoc]
  rfl

/-- The identification with the strict transform is compatible with the canonical
morphisms from `V₁' ×_U V₂`. -/
@[reassoc (attr := simp)]
lemma toImage_comparisonSpaceAdmissibleBlowupIso_hom :
    (comparisonMap (σ₁.admissibleBlowup B) σ₂).toImage ≫
        (comparisonSpaceAdmissibleBlowupIso σ₁ σ₂ B).hom =
      improvedToStrictTransform σ₁ σ₂ B := by
  rw [← cancel_mono (strictTransformComparisonι σ₁ σ₂ B), Category.assoc,
    comparisonSpaceAdmissibleBlowupIso_hom_ι, Scheme.Hom.toImage_imageι,
    improvedToStrictTransform_ι]

/-- If the strict transform of the old first projection is an isomorphism over an open
`N`, then so is the new first projection. -/
theorem isIso_comparisonFst_admissibleBlowup_restrict {N : B.I.blowup.Opens}
    (hiso : IsIso (strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap
      B.preservedOpen ∣_ N)) :
    IsIso (comparisonFst (σ₁.admissibleBlowup B) σ₂ ∣_ N) := by
  rw [← comparisonSpaceAdmissibleBlowupIso_hom_strictTransformMap, morphismRestrict_comp]
  infer_instance

/-- The density argument of `lemma-nagata-key-boundary-disjointness`, Steps 6–8: if the
strict transform of the old first projection is an isomorphism over an open containing
the closure of the transported boundary locus `π⁻¹(Z₁,₂)`, then the comparison boundary of
the improved pair lands in the self boundary of the second side. -/
theorem comparisonBoundary_admissibleBlowup_subset (hcov : O₁ ⊔ O₂ = ⊤)
    {N' : B.I.blowup.Opens}
    (hcl : closure (⇑B.I.blowupMap ⁻¹' (⇑σ₁.V.ι '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)))) ⊆
      (N' : Set B.I.blowup))
    (hiso : IsIso (strictTransformMap (comparisonFst σ₁ σ₂) B.I.blowupMap
      B.preservedOpen ∣_ N')) :
    comparisonBoundary (σ₁.admissibleBlowup B) σ₂ ⊆
      comparisonSnd (σ₁.admissibleBlowup B) σ₂ ⁻¹' σ₂.selfBoundary O₁ := by
  have hOsub : ((O₁ : Set U)ᶜ) ⊆ (O₂ : Set U) :=
    (σ₂.boundaryLoci (by rw [sup_comm]; exact hcov)).2.1
  have hproper : IsProper (comparisonFst (σ₁.admissibleBlowup B) σ₂) :=
    isProper_comparisonFst _ _
  -- the transported boundary locus
  have hpre : ⇑B.I.blowupMap ⁻¹' (⇑σ₁.V.ι '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ))) =
      ⇑(σ₁.admissibleBlowup B).V.ι ''
        (⇑(σ₁.admissibleBlowup B).ψ ⁻¹' ((O₁ : Set U)ᶜ)) :=
    (σ₁.admissibleBlowup_image_preimage B ((O₁ : Set U)ᶜ)).symm
  set D : Set (comparisonSpace (σ₁.admissibleBlowup B) σ₂) :=
    ⇑(comparisonFst (σ₁.admissibleBlowup B) σ₂) ⁻¹'
      (⇑B.I.blowupMap ⁻¹' (⇑σ₁.V.ι '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)))) with hDdef
  -- (1) the second projection of `D` lands in the self boundary of the second side
  have hmem : ∀ z ∈ D, comparisonSnd (σ₁.admissibleBlowup B) σ₂ z ∈ σ₂.selfBoundary O₁ := by
    intro z hz
    have hz' : comparisonFst (σ₁.admissibleBlowup B) σ₂ z ∈
        ⇑(σ₁.admissibleBlowup B).V.ι ''
          (⇑(σ₁.admissibleBlowup B).ψ ⁻¹' ((O₁ : Set U)ᶜ)) := by
      rw [← hpre]
      exact hz
    have hzV : z ∈ ⇑(comparisonFst (σ₁.admissibleBlowup B) σ₂) ⁻¹'
        ((σ₁.admissibleBlowup B).V : Set (σ₁.admissibleBlowup B).X) := by
      obtain ⟨v, -, hv⟩ := hz'
      rw [Set.mem_preimage, ← hv, ← Scheme.Opens.range_ι]
      exact ⟨v, rfl⟩
    rw [← range_toImage_comparisonMap] at hzV
    obtain ⟨w, rfl⟩ := hzV
    obtain ⟨v, hv, hvw⟩ := hz'
    have hveq : v = pullback.fst (σ₁.admissibleBlowup B).ψ σ₂.ψ w := by
      apply (σ₁.admissibleBlowup B).V.ι.isOpenEmbedding.injective
      rw [hvw, comparisonFst_toImage_apply]
    rw [comparisonSnd_toImage_apply]
    refine subset_closure ⟨pullback.snd (σ₁.admissibleBlowup B).ψ σ₂.ψ w, ?_, rfl⟩
    rw [Set.mem_preimage, ← ψ_pullback_fst_apply, ← hveq]
    exact hv
  -- (2) the comparison boundary of the improved pair is in the closure of `D`
  have hDcl : comparisonBoundary (σ₁.admissibleBlowup B) σ₂ ⊆ closure D := by
    have hsurjT : ⇑B.I.blowupMap ⁻¹' (⇑σ₁.V.ι '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ))) ⊆
        Set.range ⇑(comparisonFst (σ₁.admissibleBlowup B) σ₂) := by
      rw [hpre]
      rintro - ⟨v, hv, rfl⟩
      obtain ⟨w, hw⟩ :=
        preimage_subset_range_pullback_fst (σ₁.admissibleBlowup B) σ₂ (hOsub hv)
      exact ⟨(comparisonMap (σ₁.admissibleBlowup B) σ₂).toImage w, by
        rw [comparisonFst_toImage_apply, hw]⟩
    have himg : closure (⇑B.I.blowupMap ⁻¹' (⇑σ₁.V.ι '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)))) ⊆
        ⇑(comparisonFst (σ₁.admissibleBlowup B) σ₂) '' closure D := by
      refine closure_minimal ?_
        ((comparisonFst (σ₁.admissibleBlowup B) σ₂).isClosedMap _ isClosed_closure)
      intro x hx
      obtain ⟨z', hz'⟩ := hsurjT hx
      exact ⟨z', subset_closure (by rw [hDdef, Set.mem_preimage, hz']; exact hx), hz'⟩
    intro z hz
    have hzcl : comparisonFst (σ₁.admissibleBlowup B) σ₂ z ∈
        closure (⇑B.I.blowupMap ⁻¹' (⇑σ₁.V.ι '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)))) := by
      have hz2 : comparisonFst (σ₁.admissibleBlowup B) σ₂ z ∈
          (σ₁.admissibleBlowup B).forbiddenBoundary := hz
      rwa [σ₁.admissibleBlowup_forbiddenBoundary B] at hz2
    obtain ⟨e, he, hee⟩ := himg hzcl
    have hzN : comparisonFst (σ₁.admissibleBlowup B) σ₂ z ∈ (N' : Set B.I.blowup) :=
      hcl hzcl
    have hze : z = e := injOn_comparisonFst_admissibleBlowup σ₁ σ₂ B hiso
      (by rw [Set.mem_preimage]; exact hzN)
      (by rw [Set.mem_preimage, hee]; exact hzN) hee.symm
    rwa [hze]
  exact comparisonBoundary_subset_preimage_selfBoundary hDcl hmem

end Improved

end TwoOpenSide

open TwoOpenSide in
/-- **The improved comparison** (blueprint: `proposition-compactifying-union-two-opens--1`,
parts (3) and (4); Stacks Project Tag 0F3W). There is a `V₁`-admissible blow-up
`π : X₁' ⟶ X₁` such that, for the improved pair, the first comparison projection `p₁` is
an isomorphism over an open neighbourhood of the forbidden boundary `Z̄₁,₂` of `X₁'`, and
`p₂` maps `p₁⁻¹(Z̄₁,₂)` into the self boundary `Z̄₂,₂`. The improved comparison space is
the strict transform of the old one by
`TwoOpenSide.comparisonSpaceAdmissibleBlowupIso`. -/
theorem exists_admissibleBlowup_isIso_comparisonFst_near_forbiddenBoundary [IsNoetherian S]
    {u : U ⟶ S} [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    {O₁ O₂ : U.Opens} (σ₁ : TwoOpenSide u O₁) (σ₂ : TwoOpenSide u O₂)
    (hcov : O₁ ⊔ O₂ = ⊤) :
    ∃ (B : IsAdmissible σ₁.X σ₁.V) (N : (σ₁.admissibleBlowup B).X.Opens),
      (σ₁.admissibleBlowup B).forbiddenBoundary ⊆ (N : Set (σ₁.admissibleBlowup B).X) ∧
      IsIso (comparisonFst (σ₁.admissibleBlowup B) σ₂ ∣_ N) ∧
      comparisonBoundary (σ₁.admissibleBlowup B) σ₂ ⊆
        comparisonSnd (σ₁.admissibleBlowup B) σ₂ ⁻¹' σ₂.selfBoundary O₁ := by
  have hXN := σ₁.isNoetherian_X
  have hqs : QuasiSeparatedSpace σ₁.X :=
    ⟨fun _ _ _ _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have := isProper_comparisonFst σ₁ σ₂
  have hOsub : ((O₁ : Set U)ᶜ) ⊆ (O₂ : Set U) :=
    (σ₂.boundaryLoci (by rw [sup_comm]; exact hcov)).2.1
  have hTU : ⇑σ₁.V.ι '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)) ⊆ (σ₁.V : Set σ₁.X) := by
    rintro - ⟨v, -, rfl⟩
    rw [← Scheme.Opens.range_ι]
    exact ⟨v, rfl⟩
  have hTcl : IsClosed (⇑σ₁.V.ι ⁻¹' (⇑σ₁.V.ι '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)))) := by
    rw [Set.preimage_image_eq _ σ₁.V.ι.isOpenEmbedding.injective]
    exact O₁.isOpen.isClosed_compl.preimage σ₁.ψ.continuous
  have hTN : ⇑σ₁.V.ι '' (⇑σ₁.ψ ⁻¹' ((O₁ : Set U)ᶜ)) ⊆ (isoOpen σ₁ σ₂ : Set σ₁.X) := by
    rw [isoOpen_eq_image]
    exact Set.image_mono (Set.preimage_mono hOsub)
  -- Stacks Project Tag 0F3W applied to the proper first comparison projection
  obtain ⟨B, N', hcl, hiso⟩ :=
    exists_admissibleBlowup_isIso_strictTransformMap_near_closure
      (TopologicalSpace.NoetherianSpace.isCompact _) (comparisonFst σ₁ σ₂) hTU hTcl hTN
      (isIso_comparisonFst_restrict_isoOpen σ₁ σ₂)
  refine ⟨B, N', ?_, isIso_comparisonFst_admissibleBlowup_restrict σ₁ σ₂ B hiso,
    comparisonBoundary_admissibleBlowup_subset σ₁ σ₂ B hcov hcl hiso⟩
  rw [σ₁.admissibleBlowup_forbiddenBoundary B]
  exact hcl

open TwoOpenSide in
/-- **Improved comparison and key disjointness** (blueprint:
`proposition-compactifying-union-two-opens--1`). For prepared sides `σ₁, σ₂` there is a further
`V₁`-admissible blow-up of `X₁` such that the improved first side is still prepared, the
first projection `p₁ : X₁₂ ⟶ X₁` of the improved comparison space is an isomorphism over
an open neighbourhood of the forbidden boundary `Z̄₁,₂`, and the key disjointness
`X₁₂ ∩ (Z̄₁,₂ ×_S Z̄₂,₁) = ∅` holds. -/
theorem exists_prepared_keyDisjoint_isIso_near_twoOpenSide [IsNoetherian S] (u : U ⟶ S)
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u] (O₁ O₂ : U.Opens)
    (hcov : O₁ ⊔ O₂ = ⊤) [HasCompactification (O₁.ι ≫ u)]
    [HasCompactification (O₂.ι ≫ u)] :
    ∃ (σ₁ : TwoOpenSide u O₁) (σ₂ : TwoOpenSide u O₂) (B : IsAdmissible σ₁.X σ₁.V),
      σ₁.Prepared O₂ ∧ σ₂.Prepared O₁ ∧ (σ₁.admissibleBlowup B).Prepared O₂ ∧
      KeyDisjoint (σ₁.admissibleBlowup B) σ₂ ∧
      ∃ N : (σ₁.admissibleBlowup B).X.Opens,
        (σ₁.admissibleBlowup B).forbiddenBoundary ⊆ (N : Set (σ₁.admissibleBlowup B).X) ∧
        IsIso (comparisonFst (σ₁.admissibleBlowup B) σ₂ ∣_ N) := by
  obtain ⟨σ₁, h₁⟩ := exists_prepared_twoOpenSide u O₁ O₂ hcov
  obtain ⟨σ₂, h₂⟩ := exists_prepared_twoOpenSide u O₂ O₁ (by rw [sup_comm]; exact hcov)
  obtain ⟨B, N, hN, hiso, hB⟩ :=
    exists_admissibleBlowup_isIso_comparisonFst_near_forbiddenBoundary σ₁ σ₂ hcov
  exact ⟨σ₁, σ₂, B, h₁, h₂, TwoOpenSide.Prepared.admissibleBlowup σ₁ B h₁,
    keyDisjoint_of_comparisonBoundary_subset h₂ hB, N, hN, hiso⟩

end AlgebraicGeometry
