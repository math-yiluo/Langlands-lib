/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.CommonModification
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!

# Density of the common open in a common modification

Let `cm` be a common modification of two models `X₁`, `X₂` of a common open `U`
(`AlgebraicGeometry.CommonModification`), with open immersion `cm.j : U ⟶ cm.W`. We show that
density of `U` in both models is inherited by `cm.W`, both topologically and
scheme-theoretically.

The arguments are local on `cm.W`: the two modified models form an open cover of `cm.W`,
`cm.j` restricts on them to the lifts `cm.u₁`, `cm.u₂`, and those are dense since admissible
blow-ups preserve density.

## Main results

- `AlgebraicGeometry.dense_range_of_cover₂`,
  `AlgebraicGeometry.quasiCompact_of_cover₂`,
  `AlgebraicGeometry.isSchemeTheoreticallyDominant_of_cover₂`: density, quasi-compactness
  and scheme-theoretic density of an open immersion can be checked on a cover by two opens.
- `AlgebraicGeometry.CommonModification.dense_range_j_of_qcqs`,
  `AlgebraicGeometry.CommonModification.isSchemeTheoreticallyDominant_j`
  (blueprint: `lemma-gluing-after-admissible-blow-ups--1`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- If `j : U ⟶ W` factors as `uᵢ ≫ kᵢ` through two open immersions `kᵢ` covering `W` and
each `uᵢ` has dense range, then `j` has dense range. -/
theorem dense_range_of_cover₂ {U W A B : Scheme.{u}} (j : U ⟶ W) (k₁ : A ⟶ W) (k₂ : B ⟶ W)
    (hcover : Set.range k₁ ∪ Set.range k₂ = Set.univ) (u₁ : U ⟶ A) (u₂ : U ⟶ B)
    (h₁ : u₁ ≫ k₁ = j) (h₂ : u₂ ≫ k₂ = j) (hd₁ : Dense (Set.range u₁))
    (hd₂ : Dense (Set.range u₂)) : Dense (Set.range j) := by
  rw [dense_iff_inter_open]
  rintro O hO ⟨w₀, hw₀⟩
  have chartCase {A' : Scheme.{u}} (k : A' ⟶ W) (v : U ⟶ A') (hd : Dense (Set.range v))
      (hv : v ≫ k = j) (hk : w₀ ∈ Set.range k) : (O ∩ Set.range j).Nonempty := by
    obtain ⟨a₀, rfl⟩ := hk
    obtain ⟨-, haO, y, rfl⟩ := dense_iff_inter_open.mp hd (k ⁻¹' O)
      (hO.preimage k.continuous) ⟨a₀, hw₀⟩
    refine ⟨j y, ?_, y, rfl⟩
    rwa [← hv, Scheme.Hom.comp_apply]
  have hw₀cov : w₀ ∈ Set.range k₁ ∪ Set.range k₂ := by
    rw [hcover]
    trivial
  obtain hk | hk := hw₀cov
  · exact chartCase k₁ u₁ hd₁ h₁ hk
  · exact chartCase k₂ u₂ hd₂ h₂ hk

/-- Two open immersions with jointly surjective ranges give an open cover indexed by
`Bool`. -/
lemma iSup_cond_opensRange_eq_top {W A B : Scheme.{u}} (k₁ : A ⟶ W) (k₂ : B ⟶ W)
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    (hcover : Set.range k₁ ∪ Set.range k₂ = Set.univ) :
    ⨆ b : Bool, cond b k₁.opensRange k₂.opensRange = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Set.range k₁ ∪ Set.range k₂ := by
    rw [hcover]
    trivial
  obtain hx | hx := hx
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, hx⟩
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, hx⟩

/-- If `j = u ≫ k` with `k` an open immersion, then `k⁻¹ (j U) = u U`. -/
lemma preimage_opensRange_of_comp_eq {U W A : Scheme.{u}} (j : U ⟶ W) (k : A ⟶ W)
    (u : U ⟶ A) [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion u]
    (h : u ≫ k = j) : k ⁻¹ᵁ j.opensRange = u.opensRange := by
  subst h
  refine TopologicalSpace.Opens.ext ?_
  rw [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange, Scheme.Hom.coe_opensRange,
    Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.preimage_image_eq _ k.isOpenEmbedding.injective]

/-- If `j = u ≫ k` with `k` an open immersion, then `j⁻¹ (k A) = U`. -/
lemma preimage_opensRange_eq_top_of_comp_eq {U W A : Scheme.{u}} (j : U ⟶ W) (k : A ⟶ W)
    (u : U ⟶ A) [IsOpenImmersion k] (h : u ≫ k = j) : j ⁻¹ᵁ k.opensRange = ⊤ := by
  subst h
  rw [eq_top_iff]
  intro x _
  exact ⟨u x, by rw [← Scheme.Hom.comp_apply]⟩

/-- If `j = u ≫ k` with `k` an open immersion, the restriction of `j` to the range of `k`
is isomorphic to `u` as an arrow. -/
noncomputable def morphismRestrictOpensRangeArrowIso {U W A : Scheme.{u}} (j : U ⟶ W)
    (k : A ⟶ W) (u : U ⟶ A) [IsOpenImmersion k] (h : u ≫ k = j) :
    Arrow.mk (j ∣_ k.opensRange) ≅ Arrow.mk u :=
  morphismRestrictArrowIso j (e := 𝟙 U) u (by rw [Category.id_comp, h])
    ((preimage_opensRange_eq_top_of_comp_eq j k u h).trans
      (Scheme.Hom.opensRange_of_isIso (𝟙 U)).symm)

/-- Quasi-compactness of `j : U ⟶ W` can be checked on two open immersions covering `W`
through which `j` factors. -/
theorem quasiCompact_of_cover₂ {U W A B : Scheme.{u}} (j : U ⟶ W) (k₁ : A ⟶ W) (k₂ : B ⟶ W)
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    (hcover : Set.range k₁ ∪ Set.range k₂ = Set.univ) (u₁ : U ⟶ A) (u₂ : U ⟶ B)
    (h₁ : u₁ ≫ k₁ = j) (h₂ : u₂ ≫ k₂ = j) [QuasiCompact u₁] [QuasiCompact u₂] :
    QuasiCompact j := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @QuasiCompact) _
    (iSup_cond_opensRange_eq_top k₁ k₂ hcover)]
  rintro (_ | _)
  · rw [Bool.cond_false, MorphismProperty.arrow_mk_iso_iff (P := @QuasiCompact)
      (morphismRestrictOpensRangeArrowIso j k₂ u₂ h₂)]
    infer_instance
  · rw [Bool.cond_true, MorphismProperty.arrow_mk_iso_iff (P := @QuasiCompact)
      (morphismRestrictOpensRangeArrowIso j k₁ u₁ h₁)]
    infer_instance

/-- If `j = u ≫ k` with `j`, `k` open immersions and `j` quasi-compact, the kernel of `j`
pulls back along `k` to the kernel of `u`. -/
lemma comap_ker_of_comp_eq {U W A : Scheme.{u}} (j : U ⟶ W) (k : A ⟶ W) (u : U ⟶ A)
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion k] [IsOpenImmersion u]
    (h : u ≫ k = j) : j.ker.comap k = u.ker :=
  (Scheme.Hom.ker_of_isPullback j k (IsOpenImmersion.isPullback (𝟙 U) u j k
    (by rw [Category.id_comp, h]) (preimage_opensRange_of_comp_eq j k u h))).symm

/-- An inclusion of ideal sheaves can be checked after pullback along two open immersions
jointly covering the scheme. -/
lemma Scheme.IdealSheafData.le_of_comap_le₂ {W A B : Scheme.{u}} (k₁ : A ⟶ W) (k₂ : B ⟶ W)
    [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    (hcover : Set.range k₁ ∪ Set.range k₂ = Set.univ) {I J : W.IdealSheafData}
    (H₁ : I.comap k₁ ≤ J.comap k₁) (H₂ : I.comap k₂ ≤ J.comap k₂) : I ≤ J := by
  let k : ∀ b : Bool, cond b A B ⟶ W := fun b ↦ match b with
    | true => k₁
    | false => k₂
  have hk : ∀ b, IsOpenImmersion (k b) := fun b ↦ match b with
    | true => ‹IsOpenImmersion k₁›
    | false => ‹IsOpenImmersion k₂›
  refine Scheme.IdealSheafData.le_of_forall_comap_le k ?_ fun b ↦ match b with
    | true => H₁
    | false => H₂
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Set.range k₁ ∪ Set.range k₂ := by
    rw [hcover]
    trivial
  obtain hx | hx := hx
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨true, hx⟩
  · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, hx⟩

/-- Scheme-theoretic density of an open immersion `j : U ⟶ W` can be checked on two open
immersions covering `W` through which `j` factors. -/
theorem isSchemeTheoreticallyDominant_of_cover₂ {U W A B : Scheme.{u}} (j : U ⟶ W)
    (k₁ : A ⟶ W) (k₂ : B ⟶ W) [IsOpenImmersion j] [IsOpenImmersion k₁] [IsOpenImmersion k₂]
    (hcover : Set.range k₁ ∪ Set.range k₂ = Set.univ) (u₁ : U ⟶ A) (u₂ : U ⟶ B)
    (h₁ : u₁ ≫ k₁ = j) (h₂ : u₂ ≫ k₂ = j) [IsOpenImmersion u₁] [IsOpenImmersion u₂]
    [QuasiCompact u₁] [QuasiCompact u₂] [IsSchemeTheoreticallyDominant u₁]
    [IsSchemeTheoreticallyDominant u₂] : IsSchemeTheoreticallyDominant j := by
  have := quasiCompact_of_cover₂ j k₁ k₂ hcover u₁ u₂ h₁ h₂
  refine ⟨le_antisymm (Scheme.IdealSheafData.le_of_comap_le₂ k₁ k₂ hcover ?_ ?_) bot_le⟩
  · rw [comap_ker_of_comp_eq j k₁ u₁ h₁, Scheme.Hom.ker_eq_bot u₁]
    exact bot_le
  · rw [comap_ker_of_comp_eq j k₂ u₂ h₂, Scheme.Hom.ker_eq_bot u₂]
    exact bot_le

namespace IsAdmissible

/-- If `j : U ⟶ X` is a quasi-compact, scheme-theoretically dense open immersion and `B` is a
`j(U)`-admissible blow-up, then any open immersion `u : U ⟶ Bl` onto the preimage of `j(U)`
is scheme-theoretically dense. -/
lemma isSchemeTheoreticallyDominant_of_range_eq {X U : Scheme.{u}} {j : U ⟶ X}
    [IsOpenImmersion j] [QuasiCompact j] [IsSchemeTheoreticallyDominant j]
    (B : IsAdmissible X j.opensRange) (u : U ⟶ B.I.blowup) [IsOpenImmersion u]
    (hrange : Set.range u = B.I.blowupMap ⁻¹' Set.range j) :
    IsSchemeTheoreticallyDominant u := by
  have hι : j.opensRange.ι = j.isoOpensRange.inv ≫ j :=
    ((Iso.inv_comp_eq _).mpr j.isoOpensRange_hom_ι.symm).symm
  have : QuasiCompact j.opensRange.ι := by
    rw [hι]
    infer_instance
  have : IsSchemeTheoreticallyDominant j.opensRange.ι := by
    rw [hι]
    infer_instance
  have := B.isSchemeTheoreticallyDominant_preimage_ι
  have hr : Set.range u = Set.range (B.I.blowupMap ⁻¹ᵁ j.opensRange).ι := by
    rw [hrange, Scheme.Opens.range_ι]
    rfl
  rw [← IsOpenImmersion.isoOfRangeEq_hom_fac u _ hr]
  infer_instance

end IsAdmissible

namespace CommonModification

variable {S U X₁ X₂ : Scheme.{u}} {s₁ : X₁ ⟶ S} {s₂ : X₂ ⟶ S} {j₁ : U ⟶ X₁} {j₂ : U ⟶ X₂}
  [IsOpenImmersion j₁] [IsOpenImmersion j₂]

/-- Blueprint `lemma-gluing-after-admissible-blow-ups--1`: Density of the common open in a common
modification (topological part).

If `U` is dense in both qcqs models `X₁`, `X₂`, then it is dense in the common
modification. -/
theorem dense_range_j_of_qcqs (cm : CommonModification s₁ s₂ j₁ j₂) [CompactSpace X₁]
    [QuasiSeparatedSpace X₁] [CompactSpace X₂] [QuasiSeparatedSpace X₂]
    (h₁ : Dense (Set.range j₁)) (h₂ : Dense (Set.range j₂)) : Dense (Set.range cm.j) := by
  refine dense_range_of_cover₂ cm.j cm.k₁ cm.k₂ cm.cover cm.u₁ cm.u₂ cm.u₁_k₁ cm.u₂_k₂ ?_ ?_
  · rw [cm.range_u₁]
    exact cm.B₁.dense_preimage_blowupMap_of_qcqs h₁
  · rw [cm.range_u₂]
    exact cm.B₂.dense_preimage_blowupMap_of_qcqs h₂

/-- The lift `cm.u₁` of a quasi-compact `j₁` is quasi-compact. -/
lemma quasiCompact_u₁ (cm : CommonModification s₁ s₂ j₁ j₂) [QuasiCompact j₁] :
    QuasiCompact cm.u₁ := by
  have := cm.B₁.isProper_blowupMap
  have : QuasiCompact (cm.u₁ ≫ cm.B₁.I.blowupMap) := by
    rw [cm.u₁_blowupMap]
    infer_instance
  exact .of_comp _ cm.B₁.I.blowupMap

/-- The lift `cm.u₂` of a quasi-compact `j₂` is quasi-compact. -/
lemma quasiCompact_u₂ (cm : CommonModification s₁ s₂ j₁ j₂) [QuasiCompact j₂] :
    QuasiCompact cm.u₂ := by
  have := cm.B₂.isProper_blowupMap
  have : QuasiCompact (cm.u₂ ≫ cm.B₂.I.blowupMap) := by
    rw [cm.u₂_blowupMap]
    infer_instance
  exact .of_comp _ cm.B₂.I.blowupMap

/-- The open immersion `cm.j` of a common modification of quasi-compact open immersions is
quasi-compact. -/
lemma quasiCompact_j (cm : CommonModification s₁ s₂ j₁ j₂) [QuasiCompact j₁]
    [QuasiCompact j₂] : QuasiCompact cm.j := by
  have := cm.quasiCompact_u₁
  have := cm.quasiCompact_u₂
  exact quasiCompact_of_cover₂ cm.j cm.k₁ cm.k₂ cm.cover cm.u₁ cm.u₂ cm.u₁_k₁ cm.u₂_k₂

/-- Blueprint `lemma-gluing-after-admissible-blow-ups--1`: Density of the common open in a common
modification (scheme-theoretic part).

If the quasi-compact open immersions `j₁`, `j₂` are scheme-theoretically dense, then so is
the open immersion `cm.j : U ⟶ cm.W` into the common modification. -/
theorem isSchemeTheoreticallyDominant_j (cm : CommonModification s₁ s₂ j₁ j₂)
    [QuasiCompact j₁] [QuasiCompact j₂] [IsSchemeTheoreticallyDominant j₁]
    [IsSchemeTheoreticallyDominant j₂] : IsSchemeTheoreticallyDominant cm.j := by
  have := cm.quasiCompact_u₁
  have := cm.quasiCompact_u₂
  have := cm.B₁.isSchemeTheoreticallyDominant_of_range_eq cm.u₁ cm.range_u₁
  have := cm.B₂.isSchemeTheoreticallyDominant_of_range_eq cm.u₂ cm.range_u₂
  exact isSchemeTheoreticallyDominant_of_cover₂ cm.j cm.k₁ cm.k₂ cm.cover cm.u₁ cm.u₂
    cm.u₁_k₁ cm.u₂_k₂

end CommonModification

end AlgebraicGeometry
