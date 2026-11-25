/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Blowup.FiniteDegree.Generation
public import WeilConjectures.Blowup.FiniteDegree.UniformNumerator
import all WeilConjectures.Blowup.FiniteDegree.LocalAlgebra

/-!
# Finite-degree approximation on the blow-up

For finite-type centers `I` on a qcqs scheme `X` and `J` on the blow-up of `I`, there are
`d ≥ 1` and a finite-type `L ≤ I^d` whose inverse image ideal on the blow-up is `I_E^d · J`
(`AlgebraicGeometry.Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup`, Stacks Project
Tag 0803).
-/

@[expose] public section

noncomputable section
universe u

open CategoryTheory Limits

namespace AlgebraicGeometry
section Main

variable {X : Scheme.{u}}

/-- Pullback of a finite supremum of ideal sheaves. -/
private lemma comap_finset_sup {Y : Scheme.{u}} {α : Type*} (T : Finset α)
    (F : α → X.IdealSheafData) (f : Y ⟶ X) :
    (T.sup F).comap f = T.sup fun a ↦ (F a).comap f := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T' ha ih =>
    rw [Finset.sup_insert, Finset.sup_insert, Scheme.IdealSheafData.comap_sup, ih]

/-- **Membership of a numerator in the maximal candidate** (pushforward part): if all
chart fractions of a section `m ∈ I(V)ᵈ` lie in the chart models of `J`, then `m` is a
section of the pushforward of `I_Eᵈ · J`. -/
lemma Scheme.IdealSheafData.mem_ideal_map_pow_mul_of_chartFrac_mem
    (I : X.IdealSheafData) [QuasiCompact I.blowupMap] (J : I.blowup.IdealSheafData)
    (V : X.affineOpens) {s : Finset Γ(X, V.1)}
    (hs : Ideal.span (s : Set Γ(X, V.1)) = I.ideal V)
    {d : ℕ} {m : Γ(X, V.1)} (hm : m ∈ (I.ideal V) ^ d)
    (hchart : ∀ (b : Γ(X, V.1)) (hbs : b ∈ s),
      AffineBlowup.chartFrac (I.ideal V) (hs ▸ Ideal.subset_span hbs) hm ∈
        I.chartIdeal J V (hs ▸ Ideal.subset_span hbs)) :
    m ∈ (((I.comap I.blowupMap) ^ d * J).map I.blowupMap).ideal V := by
  refine Scheme.IdealSheafData.mem_ideal_map_of_probes _ I.blowupMap V m
    (c := fun b' : ↥s ↦ I.blowupChart V (hs ▸ Ideal.subset_span b'.2))
    (I.preimage_subset_iUnion_range_blowupChart V hs)
    (fun b' ↦ I.blowupChart_comp_blowupMap_preimage V (hs ▸ Ideal.subset_span b'.2)) ?_
  intro b'
  exact mem_of_ringHom_eq
    (I.appLE_blowupChart_comp_blowupMap V (hs ▸ Ideal.subset_span b'.2)
      (I.blowupChart_comp_blowupMap_preimage V (hs ▸ Ideal.subset_span b'.2)))
    (I.blowupChartSection_mem_of_chartFrac_mem J V (hs ▸ Ideal.subset_span b'.2) hm
      (hchart b'.1 b'.2))

/-- **The chart images at a finite affine cover of the base cover the blow-up.** -/
lemma Scheme.IdealSheafData.iSup_blowupChart_image_top_eq_top
    (I : X.IdealSheafData) {t : Finset X.affineOpens}
    (ht : Set.univ ⊆ ⋃ V ∈ t, (V.1 : Set X))
    (s : ∀ V : X.affineOpens, Finset Γ(X, V.1))
    (hs : ∀ V : X.affineOpens, Ideal.span (s V : Set Γ(X, V.1)) = I.ideal V) :
    (⨆ p : Σ V : { V // V ∈ t }, { b // b ∈ s V.1 },
      I.blowupChart p.1.1 ((hs p.1.1) ▸ Ideal.subset_span p.2.2) ''ᵁ ⊤) = ⊤ := by
  rw [eq_top_iff]
  have h1 : (⊤ : I.blowup.Opens) ≤ ⨆ V : { V // V ∈ t }, I.blowupMap ⁻¹ᵁ V.1.1 := by
    intro x _
    obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (I.blowupMap x)))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hVt⟩, hxV⟩
  refine le_trans h1 (iSup_le fun V ↦ ?_)
  refine le_trans (I.preimage_le_iSup_opensRange_blowupChart V.1 (hs V.1))
    (iSup_le fun b ↦ le_iSup_of_le ⟨V, b⟩ ?_)
  intro x hx
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, trivial, hz⟩

/-- **Finite-degree approximation on the blow-up itself** (Stacks Project Tag 0803;
blueprint: `lemma:nagata-proj-closed-center-finite-degree-exists`).

The candidate for `L` at degree `d` is a finite-type subsheaf of
`(I^d) ⊓ ((I_E^d * J).map I.blowupMap)` through the finitely many chart numerators of
`AffineBlowup.exists_uniform_numerator_finset`, which generate `I_E^d · J` chart by
chart for `d` large. -/
theorem Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : I.ofFiniteType) (J : I.blowup.IdealSheafData)
    (hJ : J.ofFiniteType) :
    ∃ (d : ℕ) (L : X.IdealSheafData), 0 < d ∧ L.ofFiniteType ∧ L ≤ I ^ d ∧
      L.comap I.blowupMap = (I.comap I.blowupMap) ^ d * J := by
  classical
  have : QuasiCompact I.blowupMap := Scheme.IdealSheafData.quasiCompact_blowupMap hI
  -- a finite affine cover of `X`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens ↦ (V.1 : Set X)) (fun V ↦ V.1.isOpen) (by
      intro x _
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X] at hx
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨V, hV⟩)
  -- generators of the center over each affine open
  choose s hs using fun V : X.affineOpens ↦ hI V le_top
  -- generators of the chart models of `J`
  choose G hG using fun (V : X.affineOpens) (b : Γ(X, V.1)) (hb : b ∈ I.ideal V) ↦
    I.chartIdeal_fg hJ V hb
  -- per-cover-member uniform thresholds and numerator finsets, at the ring level
  choose d₀f hd₀f using fun V : X.affineOpens ↦
    AffineBlowup.exists_uniform_numerator_finset (I.ideal V) (s V) (hs V)
      (fun b hb ↦ I.chartIdeal J V hb)
      (fun a b ha hb ↦ I.chartIdeal_map_awayMap J V ha hb)
      (G V) (fun b hb ↦ hG V b hb)
  -- one global degree dominating all thresholds
  refine ⟨1 + t.sup d₀f, ?_⟩
  set D : ℕ := 1 + t.sup d₀f with hD
  -- the numerator finsets at the global degree
  choose M hM₁ hM₂ using fun (V : X.affineOpens) (hVt : V ∈ t) ↦
    hd₀f V D (le_trans (Finset.le_sup hVt) (Nat.le_add_left _ 1))
  -- membership of the numerators in the maximal candidate
  have hmC : ∀ (V : X.affineOpens) (hVt : V ∈ t), ∀ m ∈ M V hVt,
      m ∈ (I ^ D ⊓ (((I.comap I.blowupMap) ^ D * J).map I.blowupMap)).ideal V := by
    intro V hVt m hmM
    obtain ⟨hmI, hchart⟩ := hM₁ V hVt m hmM
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · have heq : (I ^ D).ideal V = (I.ideal V) ^ D := by
        rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
      exact heq.ge hmI
    · exact I.mem_ideal_map_pow_mul_of_chartFrac_mem J V (hs V) hmI hchart
  -- extraction of a finite-type subsheaf through the numerators, per cover member
  have hLV : ∀ (V : X.affineOpens), V ∈ t → ∃ LV : X.IdealSheafData,
      LV ≤ I ^ D ⊓ (((I.comap I.blowupMap) ^ D * J).map I.blowupMap) ∧
      LV.ofFiniteType ∧ ∀ (hVt : V ∈ t),
        LV.ideal V = Ideal.span (M V hVt : Set Γ(X, V.1)) := by
    intro V hVt
    obtain ⟨LV, h1, h2, h3⟩ := Scheme.IdealSheafData.exists_finiteType_le_ideal_eq
      (I ^ D ⊓ (((I.comap I.blowupMap) ^ D * J).map I.blowupMap)) V
      (F := Ideal.span (M V hVt : Set Γ(X, V.1)))
      ⟨_, rfl⟩ (by
        rw [Ideal.span_le]
        intro x hx
        exact hmC V hVt x (Finset.mem_coe.mp hx))
    exact ⟨LV, h1, h2, fun _ ↦ h3⟩
  choose LV hLVle hLVft hLVid using hLV
  refine ⟨t.attach.sup fun V ↦ LV V.1 V.2,
    Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _), ?_, ?_, ?_⟩
  · -- finite type: finite supremum of finite-type subsheaves
    exact Finset.sup_induction Scheme.IdealSheafData.ofFiniteType_bot
      (fun _ ha _ hb ↦ Scheme.IdealSheafData.ofFiniteType.sup ha hb)
      fun V _ ↦ hLVft V.1 V.2
  · -- contained in `I ^ D`
    exact Finset.sup_le fun V _ ↦ (hLVle V.1 V.2).trans inf_le_left
  · -- the inverse image ideal is `I_E^D · J`
    apply le_antisymm
    · -- `≤`: from the pushforward bound, by the Galois connection
      rw [comap_finset_sup]
      refine Finset.sup_le fun V _ ↦ ?_
      have h1 : LV V.1 V.2 ≤ ((I.comap I.blowupMap) ^ D * J).map I.blowupMap :=
        (hLVle V.1 V.2).trans inf_le_right
      exact ((Scheme.IdealSheafData.comap_mono I.blowupMap) h1).trans
        (Scheme.IdealSheafData.comap_map_le _ _)
    · -- `≥`: chartwise generation by the numerators
      refine Scheme.IdealSheafData.le_of_iSup_eq_top
        (fun p : Σ V : { V // V ∈ t }, { b // b ∈ s V.1 } ↦
          ⟨I.blowupChart p.1.1 ((hs p.1.1) ▸ Ideal.subset_span p.2.2) ''ᵁ ⊤,
            (isAffineOpen_top _).image_of_isOpenImmersion _⟩) ?_ ?_
      · -- the chart images cover the blow-up
        exact I.iSup_blowupChart_image_top_eq_top ht s hs
      · -- the generation inequality on each chart
        rintro ⟨⟨V, hVt⟩, b'⟩
        refine Scheme.IdealSheafData.ideal_pow_mul_le_comap_of_numerators I J _ V
          ((hs V) ▸ Ideal.subset_span b'.2) D
          (G V b'.1 ((hs V) ▸ Ideal.subset_span b'.2))
          (hG V b'.1 ((hs V) ▸ Ideal.subset_span b'.2)) ?_
        intro μ0 hμ0
        obtain ⟨m0, hm0M, heq⟩ := hM₂ V hVt b'.1 b'.2 μ0 hμ0
        refine ⟨m0, ?_, heq⟩
        have h1 : m0 ∈ (LV V hVt).ideal V := by
          rw [hLVid V hVt hVt]
          exact Ideal.subset_span (Finset.mem_coe.mpr hm0M)
        have h2 : LV V hVt ≤ t.attach.sup fun V' ↦ LV V'.1 V'.2 :=
          Finset.le_sup (f := fun V' : { x // x ∈ t } ↦ LV V'.1 V'.2)
            (Finset.mem_attach _ ⟨V, hVt⟩)
        exact h2 V h1

end Main

end AlgebraicGeometry
