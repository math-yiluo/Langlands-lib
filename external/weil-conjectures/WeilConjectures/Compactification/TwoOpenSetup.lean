/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.Density
public import WeilConjectures.Compactification.BoundaryPreparation
public import WeilConjectures.Compactification.GraphExtension
public import WeilConjectures.Mathlib.AlgebraicGeometry.OpenImmersion

/-!

# The prepared sides of the two-open compactification theorem

This file sets up the per-side data of the two-open compactification theorem,
following the blueprint chapter "Nagata compactification", section "The two-open
compactification theorem" (proof order items 34–37 applied to the two opens):

Let `u : U ⟶ S` be separated and of finite type over a Noetherian scheme `S` and let `O`
be an open of `U`. The structure `AlgebraicGeometry.TwoOpenSide u O` records the state of
one side of the construction: a proper ambient scheme `X ⟶ S`, an open `V ⊆ X` with a
proper morphism `ψ : V ⟶ U` extending the inclusion of an embedded copy of `O`, and
density of the copy of `O` in `X`.

The other open `O'` of the two-open construction enters only through the boundary loci,
so it is a parameter of those and not of the structure itself:

* `TwoOpenSide.selfBoundary O'` — the closure in `X` of `ψ ⁻¹ (U ∖ O')`;
* `TwoOpenSide.forbiddenBoundary` — the closure in `X` of `ψ ⁻¹ (U ∖ O)`.

The predicate `TwoOpenSide.Prepared O'` states that the two boundary closures are
disjoint (blueprint: `def:nagata-two-open-prepared-boundaries`,
`lemma:nagata-prepared-boundaries`). The complement of the forbidden boundary is the
open `TwoOpenSide.interior` (the `Xᵢ°` of the blueprint), which contains the embedded
copy of `O` (`TwoOpenSide.interiorEmb`).

`TwoOpenSide.admissibleBlowup` transports a side along a `V`-admissible blow-up of the
ambient scheme; boundary loci transport to preimages
(`TwoOpenSide.admissibleBlowup_image_preimage`), so preparedness persists
(`TwoOpenSide.Prepared.admissibleBlowup`; blueprint:
`lemma:nagata-boundary-disjoint-persists`).

Finally `AlgebraicGeometry.exists_prepared_twoOpenSide` constructs a prepared side for
a compactifiable open `O` covering `U` together with `O'`: choose a
scheme-theoretically dense compactification (proof order item 34,
`exists_compactification_isSchemeTheoreticallyDominant`), extend it by the graph
construction (Stacks Project Tag 0F3Z, `Compactification.nonempty_properExtension`;
blueprint `def:nagata-two-open-graph-extensions`,
`lemma:nagata-two-open-graph-extensions`, `def:nagata-two-open-boundary-loci`,
`lemma:nagata-boundary-loci`), and separate the boundary closures by the
constructible-boundary separation blow-up (Stacks Project Tags 080P and 0F3V,
`exists_admissibleBlowup_disjoint_closures`).

-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {U S : Scheme.{u}}

/-- The data of one **side of the two-open compactification theorem** for a morphism
`u : U ⟶ S` and an open `O` of `U` (blueprint:
`def:nagata-two-open-graph-extensions`, `def:nagata-two-open-boundary-loci`).

The second open of the two-open construction plays no role in this data; it enters only
as a parameter of the boundary loci `TwoOpenSide.selfBoundary` and of the preparedness
predicate `TwoOpenSide.Prepared`. -/
structure TwoOpenSide (u : U ⟶ S) (O : U.Opens) where
  /-- The proper ambient model. -/
  X : Scheme.{u}
  /-- The structure morphism of the ambient model. -/
  s : X ⟶ S
  /-- The ambient model is proper over `S`. -/
  isProper_s : IsProper s
  /-- The open on which the proper extension of the inclusion of `O` is defined. -/
  V : X.Opens
  /-- The proper extension `ψ : V ⟶ U` of the inclusion of `O`. -/
  ψ : V.toScheme ⟶ U
  /-- The extension `ψ` is proper. -/
  isProper_ψ : IsProper ψ
  /-- `ψ` is a morphism over `S`, for the structure morphism `s` of the ambient model. -/
  ψ_u : ψ ≫ u = V.ι ≫ s
  /-- The embedded copy of `O` inside `V`. -/
  υ : O.toScheme ⟶ V.toScheme
  /-- The embedding of `O` into `V` is an open immersion. -/
  isOpenImmersion_υ : IsOpenImmersion υ
  /-- The embedding of `O` into `V` is compatible with `ψ`, i.e. `ψ` extends the inclusion
  of `O` into `U`. -/
  υ_ψ : υ ≫ ψ = O.ι
  /-- The embedded copy of `O` is exactly the part of `V` lying over `O`. -/
  range_υ : Set.range υ = ψ ⁻¹' (O : Set U)
  /-- Over `O`, the extension `ψ` is an isomorphism. -/
  isIso_ψ_restrict : IsIso (ψ ∣_ O)
  /-- The embedded copy of `O` is dense in the ambient model. -/
  dense_range : Dense (Set.range (υ ≫ V.ι))

namespace TwoOpenSide

attribute [instance] isProper_s isProper_ψ isOpenImmersion_υ isIso_ψ_restrict

variable {u : U ⟶ S} {O : U.Opens} (σ : TwoOpenSide u O)

/-- The embedded copy of `O` in the ambient scheme. -/
def embX : O.toScheme ⟶ σ.X := σ.υ ≫ σ.V.ι

instance : IsOpenImmersion σ.embX := by
  rw [embX]
  infer_instance

lemma embX_s : σ.embX ≫ σ.s = O.ι ≫ u := by
  rw [embX, Category.assoc, ← σ.ψ_u, ← Category.assoc, σ.υ_ψ]

lemma dense_range_embX : Dense (Set.range σ.embX) := σ.dense_range

/-- The ambient model of a side over a Noetherian base is Noetherian. -/
lemma isNoetherian_X [IsNoetherian S] : IsNoetherian σ.X := by
  have := σ.isProper_s
  have : IsLocallyNoetherian σ.X := LocallyOfFiniteType.isLocallyNoetherian σ.s
  have : CompactSpace σ.X := QuasiCompact.compactSpace_of_compactSpace σ.s
  exact ⟨⟩

section Boundary

/-- The **self boundary** of a side, relative to the other open `O'`: the closure in the
ambient scheme of the inverse image under `ψ` of the closed complement `U ∖ O'`.
(Blueprint: `Z̄_{i,i}` in `def:nagata-two-open-prepared-boundaries`.) -/
def selfBoundary (O' : U.Opens) : Set σ.X := closure (σ.V.ι '' (σ.ψ ⁻¹' ((O' : Set U)ᶜ)))

/-- The **forbidden boundary** of a side: the closure in the ambient scheme of the
inverse image under `ψ` of the closed complement `U ∖ O` of its own open. Removing it
yields the intermediate locus `Xᵢ°` of the blueprint.
(Blueprint: `Z̄_{i,j}` in `def:nagata-two-open-prepared-boundaries`.) -/
def forbiddenBoundary : Set σ.X := closure (σ.V.ι '' (σ.ψ ⁻¹' ((O : Set U)ᶜ)))

/-- A side is **prepared** relative to the other open `O'` if its two boundary closures
are disjoint. (Blueprint: `lemma:nagata-prepared-boundaries`.) -/
def Prepared (O' : U.Opens) : Prop := Disjoint (σ.selfBoundary O') σ.forbiddenBoundary

/-- The image in the ambient scheme of a closed boundary locus of `V` meets `V` in
exactly itself: boundary loci are closed in `V`. -/
lemma closure_image_preimage_inter {A : Set U} (hA : IsClosed A) :
    closure (σ.V.ι '' (σ.ψ ⁻¹' A)) ∩ (σ.V : Set σ.X) = σ.V.ι '' (σ.ψ ⁻¹' A) := by
  have hclosed : IsClosed (σ.ψ ⁻¹' A) := hA.preimage σ.ψ.continuous
  obtain ⟨C, hC, hCpre⟩ := σ.V.ι.isOpenEmbedding.isInducing.isClosed_iff.mp hclosed
  have himg : σ.V.ι '' (σ.ψ ⁻¹' A) = C ∩ (σ.V : Set σ.X) := by
    rw [← hCpre, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  apply subset_antisymm
  · have hsub : closure (σ.V.ι '' (σ.ψ ⁻¹' A)) ⊆ C :=
      closure_minimal (himg.le.trans Set.inter_subset_left) hC
    calc closure (σ.V.ι '' (σ.ψ ⁻¹' A)) ∩ (σ.V : Set σ.X)
        ⊆ C ∩ (σ.V : Set σ.X) := Set.inter_subset_inter hsub le_rfl
      _ = σ.V.ι '' (σ.ψ ⁻¹' A) := himg.symm
  · exact Set.subset_inter (subset_closure)
      (by rw [himg]; exact Set.inter_subset_right)

/-- The embedded copy of `O` avoids the forbidden boundary. -/
lemma disjoint_range_embX_forbiddenBoundary :
    Disjoint (Set.range σ.embX) σ.forbiddenBoundary := by
  rw [Set.disjoint_right]
  rintro x hx ⟨o, rfl⟩
  have hxV : σ.embX o ∈ (σ.V : Set σ.X) := by
    rw [← Scheme.Opens.range_ι]
    exact ⟨σ.υ o, rfl⟩
  have hmem : σ.embX o ∈ σ.V.ι '' (σ.ψ ⁻¹' ((O : Set U)ᶜ)) := by
    rw [← σ.closure_image_preimage_inter O.isOpen.isClosed_compl]
    exact ⟨hx, hxV⟩
  obtain ⟨w, hw, hweq⟩ := hmem
  have hwυ : w = σ.υ o := σ.V.ι.isOpenEmbedding.injective hweq
  have : σ.υ o ∈ σ.ψ ⁻¹' ((O : Set U)ᶜ) := hwυ ▸ hw
  have hmemO : σ.ψ (σ.υ o) ∈ (O : Set U) := by
    have h1 : σ.υ o ∈ Set.range σ.υ := ⟨o, rfl⟩
    rw [σ.range_υ] at h1
    exact h1
  exact this hmemO

/-- The complement of the forbidden boundary, i.e. the locus `Xᵢ°` of the blueprint.
(Blueprint: `proposition-compactifying-union-two-opens--1`.) -/
def interior : σ.X.Opens := ⟨σ.forbiddenBoundaryᶜ, isClosed_closure.isOpen_compl⟩

lemma range_embX_subset_interior : Set.range σ.embX ⊆ (σ.interior : Set σ.X) :=
  σ.disjoint_range_embX_forbiddenBoundary.subset_compl_right

/-- The embedded copy of `O` inside the complement of the forbidden boundary. -/
def interiorEmb : O.toScheme ⟶ σ.interior.toScheme :=
  IsOpenImmersion.lift σ.interior.ι σ.embX
    (by rw [Scheme.Opens.range_ι]; exact σ.range_embX_subset_interior)

@[reassoc (attr := simp)]
lemma interiorEmb_ι : σ.interiorEmb ≫ σ.interior.ι = σ.embX :=
  IsOpenImmersion.lift_fac _ _ _

instance : IsOpenImmersion σ.interiorEmb := by
  have h : IsOpenImmersion (σ.interiorEmb ≫ σ.interior.ι) := by
    rw [σ.interiorEmb_ι]
    infer_instance
  exact IsOpenImmersion.of_comp σ.interiorEmb σ.interior.ι

end Boundary

section AdmissibleBlowup

variable [IsNoetherian S] (B : IsAdmissible σ.X σ.V)

/-- **Transport of a side along a `V`-admissible blow-up** of the ambient scheme
(blueprint: `def:nagata-two-open-prepared-boundaries`,
`def:nagata-two-open-improved-comparison`).

The open `V`, the proper extension `ψ` and the embedded copy of `O` transport along the
isomorphism over `V`; density transports because the complement of the center is dense in
the blow-up. -/
def admissibleBlowup : TwoOpenSide u O :=
  have : IsIso (B.I.blowupMap ∣_ σ.V) := B.isIso_blowupMap_restrict
  have := B.isProper_blowupMap
  have := σ.isProper_s
  have := σ.isProper_ψ
  have := σ.isOpenImmersion_υ
  { X := B.I.blowup
    s := B.I.blowupMap ≫ σ.s
    isProper_s := inferInstance
    V := B.I.blowupMap ⁻¹ᵁ σ.V
    ψ := (B.I.blowupMap ∣_ σ.V) ≫ σ.ψ
    isProper_ψ := by
      rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsProper)]
      exact σ.isProper_ψ
    ψ_u := by
      rw [Category.assoc, σ.ψ_u, morphismRestrict_ι_assoc]
    υ := σ.υ ≫ inv (B.I.blowupMap ∣_ σ.V)
    isOpenImmersion_υ := inferInstance
    υ_ψ := by
      rw [Category.assoc, IsIso.inv_hom_id_assoc, σ.υ_ψ]
    range_υ := by
      have hinj : Function.Injective ⇑(B.I.blowupMap ∣_ σ.V) :=
        (Scheme.homeoOfIso (asIso (B.I.blowupMap ∣_ σ.V))).injective
      ext x
      constructor
      · rintro ⟨o, rfl⟩
        refine Set.mem_preimage.mpr ?_
        have h1 : (B.I.blowupMap ∣_ σ.V) ((σ.υ ≫ inv (B.I.blowupMap ∣_ σ.V)) o) =
            σ.υ o := by
          rw [← Scheme.Hom.comp_apply, Category.assoc, IsIso.inv_hom_id,
            Category.comp_id]
        rw [Scheme.Hom.comp_apply, h1]
        have h2 : σ.υ o ∈ Set.range σ.υ := ⟨o, rfl⟩
        rw [σ.range_υ] at h2
        exact h2
      · intro hx
        have h2 : (B.I.blowupMap ∣_ σ.V) x ∈ Set.range σ.υ := by
          rw [σ.range_υ]
          exact Set.mem_preimage.mp hx
        obtain ⟨o, ho⟩ := h2
        refine ⟨o, hinj ?_⟩
        rw [← Scheme.Hom.comp_apply, Category.assoc, IsIso.inv_hom_id,
          Category.comp_id, ho]
    isIso_ψ_restrict := by
      rw [morphismRestrict_comp]
      have := σ.isIso_ψ_restrict
      infer_instance
    dense_range := by
      have hle : (σ.υ ≫ σ.V.ι).opensRange ≤ σ.V := by
        rintro x ⟨o, rfl⟩
        change (σ.υ ≫ σ.V.ι) o ∈ (σ.V : Set σ.X)
        rw [← Scheme.Opens.range_ι]
        exact ⟨σ.υ o, (Scheme.Hom.comp_apply _ _ _).symm⟩
      have hiso : IsIso (B.I.blowupMap ∣_ (σ.υ ≫ σ.V.ι).opensRange) :=
        isIso_morphismRestrict_of_le B.I.blowupMap hle B.isIso_blowupMap_restrict
      have hq : ((σ.υ ≫ inv (B.I.blowupMap ∣_ σ.V)) ≫ (B.I.blowupMap ⁻¹ᵁ σ.V).ι) ≫
          B.I.blowupMap = σ.υ ≫ σ.V.ι := by
        rw [Category.assoc, Category.assoc, ← morphismRestrict_ι,
          IsIso.inv_hom_id_assoc]
      have hrange := range_eq_preimage_of_comp_of_isIso_restrict
        ((σ.υ ≫ inv (B.I.blowupMap ∣_ σ.V)) ≫ (B.I.blowupMap ⁻¹ᵁ σ.V).ι)
        B.I.blowupMap (σ.υ ≫ σ.V.ι) hq hiso
      have := σ.isNoetherian_X
      rw [hrange]
      exact B.dense_preimage_blowupMap σ.dense_range }

/-- Boundary loci transport along an admissible blow-up to their full preimages. -/
lemma admissibleBlowup_image_preimage (A : Set U) :
    (σ.admissibleBlowup B).V.ι '' ((σ.admissibleBlowup B).ψ ⁻¹' A) =
      B.I.blowupMap ⁻¹' (σ.V.ι '' (σ.ψ ⁻¹' A)) := by
  have : IsIso (B.I.blowupMap ∣_ σ.V) := B.isIso_blowupMap_restrict
  have hcomm : ∀ v' : (B.I.blowupMap ⁻¹ᵁ σ.V).toScheme,
      B.I.blowupMap ((B.I.blowupMap ⁻¹ᵁ σ.V).ι v') =
        σ.V.ι ((B.I.blowupMap ∣_ σ.V) v') := by
    intro v'
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]
  ext x'
  constructor
  · rintro ⟨v', hv', rfl⟩
    refine Set.mem_preimage.mpr ⟨(B.I.blowupMap ∣_ σ.V) v', ?_, (hcomm v').symm⟩
    have : (σ.admissibleBlowup B).ψ v' = σ.ψ ((B.I.blowupMap ∣_ σ.V) v') :=
      Scheme.Hom.comp_apply _ _ _
    rwa [Set.mem_preimage, ← this]
  · intro hx'
    obtain ⟨w, hw, hweq⟩ := Set.mem_preimage.mp hx'
    have hx'V : x' ∈ Set.range (B.I.blowupMap ⁻¹ᵁ σ.V).ι := by
      rw [Scheme.Opens.range_ι]
      change B.I.blowupMap x' ∈ (σ.V : Set σ.X)
      rw [← hweq, ← Scheme.Opens.range_ι]
      exact ⟨w, rfl⟩
    obtain ⟨v', rfl⟩ := hx'V
    refine ⟨v', ?_, rfl⟩
    have hwv : (B.I.blowupMap ∣_ σ.V) v' = w := by
      apply σ.V.ι.isOpenEmbedding.injective
      rw [← hcomm v', hweq]
    have : (σ.admissibleBlowup B).ψ v' = σ.ψ ((B.I.blowupMap ∣_ σ.V) v') :=
      Scheme.Hom.comp_apply _ _ _
    rwa [Set.mem_preimage, this, hwv]

lemma admissibleBlowup_selfBoundary (O' : U.Opens) :
    (σ.admissibleBlowup B).selfBoundary O' =
      closure (B.I.blowupMap ⁻¹' (σ.V.ι '' (σ.ψ ⁻¹' ((O' : Set U)ᶜ)))) := by
  change closure ((σ.admissibleBlowup B).V.ι ''
    ((σ.admissibleBlowup B).ψ ⁻¹' ((O' : Set U)ᶜ))) = _
  rw [admissibleBlowup_image_preimage]

lemma admissibleBlowup_forbiddenBoundary :
    (σ.admissibleBlowup B).forbiddenBoundary =
      closure (B.I.blowupMap ⁻¹' (σ.V.ι '' (σ.ψ ⁻¹' ((O : Set U)ᶜ)))) := by
  change closure ((σ.admissibleBlowup B).V.ι ''
    ((σ.admissibleBlowup B).ψ ⁻¹' ((O : Set U)ᶜ))) = _
  rw [admissibleBlowup_image_preimage]

/-- **Preparedness persists along admissible blow-ups**: the transported boundary
closures are contained in the preimages of the original ones, so disjointness is
preserved. (Blueprint: `lemma:nagata-boundary-disjoint-persists`; proof order
item 37.) -/
lemma Prepared.admissibleBlowup {O' : U.Opens} (hσ : σ.Prepared O') :
    (σ.admissibleBlowup B).Prepared O' := by
  have hsub : ∀ A : Set σ.X,
      closure (B.I.blowupMap ⁻¹' A) ⊆ B.I.blowupMap ⁻¹' (closure A) := fun A ↦
    closure_minimal (Set.preimage_mono subset_closure)
      (isClosed_closure.preimage B.I.blowupMap.continuous)
  change Disjoint ((σ.admissibleBlowup B).selfBoundary O')
    (σ.admissibleBlowup B).forbiddenBoundary
  rw [σ.admissibleBlowup_selfBoundary B O', σ.admissibleBlowup_forbiddenBoundary]
  exact ((hσ.preimage B.I.blowupMap).mono (hsub _) (hsub _))

end AdmissibleBlowup

end TwoOpenSide

/-- **Existence of a prepared side** (blueprint:
`def:nagata-two-open-dense-compactifications` through
`lemma:nagata-prepared-boundaries`; proof order items 34–36 applied).

Choose a scheme-theoretically dense compactification, extend it to a proper morphism to
`U` by the graph construction (Stacks Project Tag 0F3Z), and separate the two boundary
closures by the boundary-separation blow-up (Stacks Project Tag 0F3V). -/
theorem exists_prepared_twoOpenSide [IsNoetherian S] (u : U ⟶ S) [IsSeparated u]
    [LocallyOfFiniteType u] [QuasiCompact u] (O O' : U.Opens) (hcov : O ⊔ O' = ⊤)
    [HasCompactification (O.ι ≫ u)] :
    ∃ σ : TwoOpenSide u O, σ.Prepared O' := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian u
  have : CompactSpace U := QuasiCompact.compactSpace_of_compactSpace u
  have : IsNoetherian U := ⟨⟩
  have : QuasiCompact (O.ι ≫ u) := inferInstance
  -- item 34: a scheme-theoretically dense compactification of `O ⟶ S`
  obtain ⟨c, hc⟩ := exists_compactification_isSchemeTheoreticallyDominant (O.ι ≫ u)
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  -- Stacks 0F3Z: the graph extension of the compactification
  obtain ⟨B, Vgr, ψ, v, hψ, hv, hvπ, hvψ, hpre, hiso, hψu⟩ :=
    (Compactification.nonempty_properExtension u O
      (TopologicalSpace.NoetherianSpace.isCompact _) c).some
  have := hψ
  have := hv
  have := B.isProper_blowupMap
  -- the graph-extension side
  have hdense : Dense (Set.range (v ≫ Vgr.ι)) := by
    have hq : (v ≫ Vgr.ι) ≫ B.I.blowupMap = c.i := by rw [Category.assoc, hvπ]
    have hiso' : IsIso (B.I.blowupMap ∣_ c.i.opensRange) := B.isIso_blowupMap_restrict
    rw [range_eq_preimage_of_comp_of_isIso_restrict (v ≫ Vgr.ι) B.I.blowupMap c.i hq hiso']
    refine B.dense_preimage_blowupMap ?_
    have : IsSchemeTheoreticallyDominant c.i := hc
    have : QuasiCompact c.i := inferInstance
    have := Scheme.Hom.denseRange c.i
    exact this
  let σ₀ : TwoOpenSide u O :=
    { X := B.I.blowup
      s := B.I.blowupMap ≫ c.g
      isProper_s := inferInstance
      V := Vgr
      ψ := ψ
      isProper_ψ := hψ
      ψ_u := hψu
      υ := v
      isOpenImmersion_υ := hv
      υ_ψ := hvψ
      range_υ := by
        rw [← hpre]
        rfl
      isIso_ψ_restrict := hiso
      dense_range := hdense }
  -- Stacks 0F3V: separate the two boundary loci of `σ₀`
  have : IsNoetherian σ₀.X := σ₀.isNoetherian_X
  have : CompactSpace σ₀.V.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : IsNoetherian σ₀.V.toScheme := ⟨⟩
  have hT₁ : IsClosed (σ₀.ψ ⁻¹' ((O' : Set U)ᶜ)) :=
    O'.isOpen.isClosed_compl.preimage σ₀.ψ.continuous
  have hT₂ : IsClosed (σ₀.ψ ⁻¹' ((O : Set U)ᶜ)) :=
    O.isOpen.isClosed_compl.preimage σ₀.ψ.continuous
  have huniv : (O' : Set U) ∪ (O : Set U) = Set.univ := by
    have := congrArg (fun W : U.Opens ↦ (W : Set U)) hcov
    simpa [Set.union_comm] using this
  have hdisj : Disjoint (σ₀.ψ ⁻¹' ((O' : Set U)ᶜ)) (σ₀.ψ ⁻¹' ((O : Set U)ᶜ)) := by
    refine Disjoint.preimage _ ?_
    rwa [Set.disjoint_iff_inter_eq_empty, ← Set.compl_union, Set.compl_empty_iff]
  obtain ⟨B₁, hB₁⟩ := exists_admissibleBlowup_disjoint_closures
    (TopologicalSpace.NoetherianSpace.isCompact _) hT₁ hT₂
    (TopologicalSpace.NoetherianSpace.isCompact _)
    (TopologicalSpace.NoetherianSpace.isCompact _) hdisj
  refine ⟨σ₀.admissibleBlowup B₁, ?_⟩
  rw [TwoOpenSide.Prepared, σ₀.admissibleBlowup_selfBoundary B₁ O',
    σ₀.admissibleBlowup_forbiddenBoundary]
  exact hB₁

end AlgebraicGeometry
