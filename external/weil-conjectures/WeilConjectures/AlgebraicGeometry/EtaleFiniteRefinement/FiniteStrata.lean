/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleFiniteRefinement.GenericPointFinite
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Quasi-finite morphisms are finite over the strata of a stratification

`AlgebraicGeometry.Scheme.Hom.exists_stratification_isFinite`: over a Noetherian scheme `X`, a
quasi-compact separated locally quasi-finite morphism `v : V ⟶ X` of finite type becomes finite
after base change to each stratum of some stratification of `X`. By Noetherian induction on the
closed subsets `Z` of `X`: on the reduced closed subscheme of an irreducible component `C` of
`Z`, the base change of `v` is finite over a neighbourhood of the generic point
(`AlgebraicGeometry.Scheme.Hom.exists_isFinite_morphismRestrict_genericPoint`), which cuts out of
`Z` a nonempty locally closed piece with closed complement.

This is the geometric input to Stacks 03SA (constructibility of `v_! M` for étale `v`) over a
Noetherian base.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {V X : Scheme.{u}} (v : V ⟶ X)

/-- A morphism finite over an open is finite over every smaller open. -/
lemma Hom.isFinite_morphismRestrict_of_le {X S : Scheme.{u}} (f : X ⟶ S) {W W' : S.Opens}
    (h : W' ≤ W) (hW : IsFinite (f ∣_ W)) : IsFinite (f ∣_ W') := by
  have := IsZariskiLocalAtTarget.restrict hW (W.ι ⁻¹ᵁ W')
  have e := morphismRestrictRestrict f W (W.ι ⁻¹ᵁ W')
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_right.mpr h] at e
  exact (MorphismProperty.arrow_mk_iso_iff @IsFinite e).mp this

/-- A finite partition of a subset `Z` of `X` into images of immersions over which `v` is
finite. -/
def Hom.HasFinitePartitionOver (Z : Set X) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (T : ι → Scheme.{u}) (j : ∀ b, T b ⟶ X),
    (∀ b, IsImmersion (j b) ∧ IsFinite (pullback.snd v (j b)) ∧ Set.range (j b) ⊆ Z) ∧
    ∀ y ∈ Z, ∃! b, y ∈ Set.range (j b)

lemma Hom.hasFinitePartitionOver_empty : v.HasFinitePartitionOver ∅ :=
  ⟨Empty, inferInstance, Empty.elim, fun b ↦ b.elim, fun b ↦ b.elim, by simp⟩

lemma Hom.HasFinitePartitionOver.union {Z₁ Z₂ : Set X} (h : Disjoint Z₁ Z₂)
    (h₁ : v.HasFinitePartitionOver Z₁) (h₂ : v.HasFinitePartitionOver Z₂) :
    v.HasFinitePartitionOver (Z₁ ∪ Z₂) := by
  obtain ⟨ι₁, _, T₁, j₁, hj₁, hu₁⟩ := h₁
  obtain ⟨ι₂, _, T₂, j₂, hj₂, hu₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim T₁ T₂, fun | .inl b => j₁ b | .inr b => j₂ b,
    ?_, ?_⟩
  · rintro (b | b)
    · exact ⟨(hj₁ b).1, (hj₁ b).2.1, (hj₁ b).2.2.trans Set.subset_union_left⟩
    · exact ⟨(hj₂ b).1, (hj₂ b).2.1, (hj₂ b).2.2.trans Set.subset_union_right⟩
  · rintro y (hy | hy)
    · obtain ⟨b, hb, hb'⟩ := hu₁ y hy
      refine ⟨.inl b, hb, ?_⟩
      rintro (c | c) hc
      · exact congrArg _ (hb' c hc)
      · exact (h.ne_of_mem hy ((hj₂ c).2.2 hc) rfl).elim
    · obtain ⟨b, hb, hb'⟩ := hu₂ y hy
      refine ⟨.inr b, hb, ?_⟩
      rintro (c | c) hc
      · exact (h.ne_of_mem ((hj₁ c).2.2 hc) hy rfl).elim
      · exact congrArg _ (hb' c hc)

variable [LocallyQuasiFinite v] [LocallyOfFiniteType v] [IsSeparated v] [QuasiCompact v]
  [IsNoetherian X]

/-- The induction step: a nonempty closed subset `Z` contains a nonempty piece with closed
complement over which `v` is finite. -/
lemma Hom.exists_hasFinitePartitionOver_nonempty {Z : Set X} (hZ : IsClosed Z)
    (hne : Z.Nonempty) :
    ∃ Z₁ ⊆ Z, Z₁.Nonempty ∧ IsClosed (Z \ Z₁) ∧ v.HasFinitePartitionOver Z₁ := by
  classical
  obtain ⟨z, hz⟩ := hne
  -- an irreducible component `C'` of `Z`, and a nonempty open `o` of `Z` inside it
  obtain ⟨C', hC', -⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({⟨z, hz⟩} : Set Z) isIrreducible_singleton
  obtain ⟨o, ho, ⟨w, hwo⟩, hoC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C' hC'
  obtain ⟨OX, hOX, hOXo⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp ho
  -- its closure `C` in `X`, with the reduced closed subscheme structure
  let C : Set X := Subtype.val '' C'
  have hCcl : IsClosed C :=
    hZ.isClosedMap_subtype_val _ (isClosed_of_mem_irreducibleComponents C' hC')
  have hCirr : IsIrreducible C := hC'.1.image _ continuous_subtype_val.continuousOn
  have hCZ : C ⊆ Z := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hZC : Z ∩ OX ⊆ C := fun y ⟨hyZ, hyO⟩ ↦
    ⟨⟨y, hyZ⟩, hoC (by rw [← hOXo]; exact hyO), rfl⟩
  let I := IdealSheafData.vanishingIdeal ⟨C, hCcl⟩
  let ι := I.subschemeι
  have hrange : Set.range ι = C := by
    rw [IdealSheafData.range_subschemeι, IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IrreducibleSpace I.subscheme := by
    have : IrreducibleSpace (Set.range ι) := by
      rw [← isIrreducible_iff_irreducibleSpace, hrange]
      exact hCirr
    exact (Homeomorph.irreducibleSpace_iff ι.isEmbedding.toHomeomorph).mpr this
  have : IsNoetherian I.subscheme := isNoetherian_of_locallyOfFiniteType ι
  -- `v` is finite over a neighbourhood `W` of the generic point of `C`
  obtain ⟨W, hgW, hfin⟩ := (pullback.snd v ι).exists_isFinite_morphismRestrict_genericPoint
  obtain ⟨UX, hUX, hUXW⟩ := ι.isEmbedding.isInducing.isOpen_iff.mp W.isOpen
  let O : X.Opens := ⟨OX, hOX⟩ ⊓ ⟨UX, hUX⟩
  have hg : IsGenericPoint (ι (genericPoint I.subscheme)) C := by
    have := (genericPoint_spec I.subscheme).image ι.continuous
    rwa [Set.image_univ, hrange, hCcl.closure_eq] at this
  have hgO : ι (genericPoint I.subscheme) ∈ O := by
    refine ⟨(hg.mem_open_set_iff hOX).mpr ⟨w, ?_, ?_⟩, ?_⟩
    · exact ⟨w, hoC hwo, rfl⟩
    · rw [← hOXo] at hwo; exact hwo
    · change genericPoint I.subscheme ∈ ι ⁻¹' UX
      rw [hUXW]; exact hgW
  refine ⟨Z ∩ O, Set.inter_subset_left, ⟨_, hCZ hg.mem, hgO⟩, ?_, ?_⟩
  · have : Z \ (Z ∩ O) = Z ∩ (O : Set X)ᶜ := by
      ext y; simp only [Set.mem_sdiff, Set.mem_inter_iff, Set.mem_compl_iff]; tauto
    rw [this]
    exact hZ.inter O.isOpen.isClosed_compl
  -- the piece `Z ∩ O`, realized by the open `ι⁻¹ O` of the reduced subscheme
  let O' : I.subscheme.Opens := ι ⁻¹ᵁ O
  have hO'W : O' ≤ W := fun y hy ↦ by
    change y ∈ (W : Set I.subscheme)
    rw [← hUXW]; exact hy.2
  have hfin' := (pullback.snd v ι).isFinite_morphismRestrict_of_le hO'W hfin
  have H := ((isPullback_morphismRestrict (pullback.snd v ι) O').flip).paste_horiz
    (IsPullback.of_hasPullback v ι)
  have hsnd : pullback.snd v (O'.ι ≫ ι) = H.isoPullback.inv ≫ (pullback.snd v ι ∣_ O') := by
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_snd]
  refine ⟨Unit, inferInstance, fun _ ↦ O'.toScheme, fun _ ↦ O'.ι ≫ ι, fun _ ↦ ⟨inferInstance,
    by rw [hsnd]; infer_instance, ?_⟩, fun y hy ↦ ⟨(), ?_, fun _ _ ↦ rfl⟩⟩
  · rintro _ ⟨y, rfl⟩
    refine ⟨hCZ ?_, y.2⟩
    rw [← hrange]
    exact ⟨_, rfl⟩
  · obtain ⟨x, hx⟩ : y ∈ Set.range ι := by rw [hrange]; exact hZC ⟨hy.1, hy.2.1⟩
    have hxO : x ∈ O' := by
      change ι x ∈ O
      rw [hx]; exact hy.2
    exact ⟨⟨x, hxO⟩, by simpa using hx⟩

/-- Noetherian induction on the closed subsets of `X`. -/
lemma Hom.hasFinitePartitionOver_of_isClosed (Z : TopologicalSpace.Closeds X) :
    v.HasFinitePartitionOver Z := by
  induction Z using WellFoundedLT.induction with
  | _ Z ih =>
  rcases (Z : Set X).eq_empty_or_nonempty with hZ | hZ
  · rw [hZ]
    exact v.hasFinitePartitionOver_empty
  obtain ⟨Z₁, hZ₁Z, hZ₁, hcl, hP⟩ := v.exists_hasFinitePartitionOver_nonempty Z.isClosed hZ
  let Z₂ : TopologicalSpace.Closeds X := ⟨Z \ Z₁, hcl⟩
  have hlt : Z₂ < Z := by
    refine lt_of_le_of_ne (fun y hy ↦ hy.1) fun heq ↦ ?_
    obtain ⟨y, hy⟩ := hZ₁
    have : y ∈ (Z₂ : Set X) := by rw [heq]; exact hZ₁Z hy
    exact this.2 hy
  have := Scheme.Hom.HasFinitePartitionOver.union v Set.disjoint_sdiff_right hP (ih Z₂ hlt)
  rwa [Set.union_sdiff_cancel hZ₁Z] at this

/-- **Quasi-finite morphisms are finite over strata.** Over a Noetherian scheme `X`, a
quasi-compact separated locally quasi-finite morphism `v : V ⟶ X` of finite type becomes finite
after base change to each stratum of some stratification of `X`. -/
theorem Hom.exists_stratification_isFinite :
    ∃ S : Stratification X, ∀ i, IsFinite (pullback.snd v (S.immersion i)) := by
  obtain ⟨ι, _, T, j, hj, hu⟩ := v.hasFinitePartitionOver_of_isClosed ⊤
  let e := Finite.equivFin ι
  have : ∀ i, IsImmersion (j (e.symm i)) := fun i ↦ (hj _).1
  refine ⟨Stratification.ofNoetherianSpace (Nat.card ι) (fun i ↦ Set.range (j (e.symm i)))
    (fun i ↦ (j _).isLocallyClosed_range) ?_ ?_ (fun i ↦ T (e.symm i)) (fun i ↦ j (e.symm i))
    inferInstance (fun _ ↦ rfl), fun i ↦ (hj _).2.1⟩
  · refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨b, hb, -⟩ := hu y trivial
    exact Set.mem_iUnion.mpr ⟨e b, by rw [Equiv.symm_apply_apply]; exact hb⟩
  · intro i i' hii'
    refine Set.disjoint_left.mpr fun y hy hy' ↦ hii' ?_
    obtain ⟨b, -, hb'⟩ := hu y trivial
    exact e.symm.injective ((hb' _ hy).trans (hb' _ hy').symm)

end AlgebraicGeometry.Scheme
