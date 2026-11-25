/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.Topology.Constructible
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Ranges of quasi-compact morphisms

The range of a quasi-compact morphism is retrocompact
(`AlgebraicGeometry.Scheme.Hom.isRetrocompact_range`), so the range of a quasi-compact open
immersion is a constructible subset (`AlgebraicGeometry.Scheme.Hom.isConstructible_range`).

A point in the closure of the range of a quasi-compact morphism is a specialization of a
point of the range (`AlgebraicGeometry.exists_specializes_of_mem_closure_range`). This is
the topological content of Stacks Project Tag 02JQ; it is deduced from the corresponding
statement about prime spectra,
`PrimeSpectrum.exists_specializes_of_mem_closure_range_comap`.

A quasi-compact scheme is the union of finitely many affine opens
(`AlgebraicGeometry.Scheme.exists_finset_isAffineOpen_sup_eq_top`), and the inclusion of an open
and closed subscheme is quasi-compact (`AlgebraicGeometry.Scheme.Opens.quasiCompact_ι_of_isClosed`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **A point in the closure of the range of a quasi-compact morphism to an affine scheme
is a specialization of a point of the range**. This is the affine case of
`AlgebraicGeometry.exists_specializes_of_mem_closure_range`. -/
theorem exists_specializes_of_mem_closure_range_of_isAffine {T P : Scheme.{u}} (h : T ⟶ P)
    [QuasiCompact h] [IsAffine P] {z : P} (hz : z ∈ closure (Set.range h)) :
    ∃ t : T, h t ⤳ z := by
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace h
  -- `T` is compact, hence the surjective image of a single affine scheme
  obtain ⟨R, g, hg⟩ := compactSpace_iff_exists.mp ‹CompactSpace T›
  -- transport the picture to the prime spectrum of `Γ(P, ⊤)`
  let φ : Γ(P, ⊤) ⟶ R := Spec.preimage (g ≫ h ≫ P.isoSpec.hom)
  have hφ : Spec.map φ = g ≫ h ≫ P.isoSpec.hom := Spec.map_preimage _
  have hcoe : ⇑(g ≫ h ≫ P.isoSpec.hom) = ⇑P.isoSpec.hom ∘ ⇑h ∘ ⇑g := by
    simp [Scheme.Hom.comp_base]
  have hrange : Set.range (Spec.map φ) = P.isoSpec.hom '' Set.range h := by
    rw [hφ, hcoe, Set.range_comp, Set.range_comp, hg.range_eq, Set.image_univ]
  have hz' : P.isoSpec.hom z ∈ closure (Set.range (Spec.map φ)) := by
    rw [hrange]
    exact image_closure_subset_closure_image P.isoSpec.hom.continuous ⟨z, hz, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Spec R, Spec.map φ q ⤳ P.isoSpec.hom z :=
    PrimeSpectrum.exists_specializes_of_mem_closure_range_comap φ.hom hz'
  -- transport the specialization back along the isomorphism `P ≅ Spec Γ(P, ⊤)`
  have hinv (w : P) : P.isoSpec.inv (P.isoSpec.hom w) = w := by simp
  have hmap := hq.map P.isoSpec.inv.continuous
  rw [hφ, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hinv, hinv] at hmap
  exact ⟨g q, hmap⟩

/-- **A point in the closure of the range of a quasi-compact morphism is a specialization
of a point of the range** (the topological content of Stacks Project Tag 02JQ). -/
@[stacks 02JQ]
theorem exists_specializes_of_mem_closure_range {T P : Scheme.{u}} (h : T ⟶ P)
    [QuasiCompact h] {z : P} (hz : z ∈ closure (Set.range h)) : ∃ t : T, h t ⤳ z := by
  -- both hypothesis and conclusion are local on the target, so we may assume `P` affine
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  have : IsAffine V.toScheme := hV
  have : QuasiCompact (h ∣_ V) :=
    IsZariskiLocalAtTarget.restrict (P := @QuasiCompact) inferInstance V
  have hsub : V.ι ⁻¹' Set.range h ⊆ Set.range (h ∣_ V) := by
    rintro ⟨v, hvV⟩ ⟨t, ht⟩
    have htV : h t ∈ V := ht ▸ hvV
    exact ⟨⟨t, htV⟩, Subtype.ext ((morphismRestrict_base_coe h V ⟨t, htV⟩).trans ht)⟩
  have hzV' : (⟨z, hzV⟩ : V) ∈ closure (Set.range (h ∣_ V)) :=
    closure_mono hsub
      (V.ι.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage hz)
  obtain ⟨t, ht⟩ := exists_specializes_of_mem_closure_range_of_isAffine (h ∣_ V) hzV'
  refine ⟨(h ⁻¹ᵁ V).ι t, ?_⟩
  simpa [Scheme.Opens.ι_apply, morphismRestrict_base_coe] using ht.map V.ι.continuous

/-- **The range of a quasi-compact morphism is retrocompact**: its intersection with a
quasi-compact open `V` is the image of the quasi-compact preimage of `V`. -/
theorem Scheme.Hom.isRetrocompact_range {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] :
    IsRetrocompact (Set.range f.base) := fun V hV hVo ↦ by
  rw [Set.inter_comm, ← Set.image_preimage_eq_inter_range]
  exact (QuasiCompact.isCompact_preimage V hVo hV).image f.continuous

/-- The range of a quasi-compact open immersion is a constructible subset. -/
theorem Scheme.Hom.isConstructible_range {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [QuasiCompact f] : Topology.IsConstructible (Set.range f.base) :=
  f.isRetrocompact_range.isConstructible f.isOpenEmbedding.isOpen_range

/-- A quasi-compact scheme is the union of finitely many affine opens. -/
lemma Scheme.exists_finset_isAffineOpen_sup_eq_top (T : Scheme.{u}) [CompactSpace T] :
    ∃ S : Finset T.Opens, (∀ O ∈ S, IsAffineOpen O) ∧ S.sup id = ⊤ := by
  classical
  obtain ⟨s, hs, hsU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens
    (U := (⊤ : T.Opens))).1 (by simpa using isCompact_univ)
  refine ⟨hs.toFinset.image Subtype.val, ?_, le_antisymm le_top ?_⟩
  · simp only [Finset.mem_image, Set.Finite.mem_toFinset]
    rintro _ ⟨O, -, rfl⟩
    exact O.2
  · rw [hsU]
    exact iSup₂_le fun i hi ↦ Finset.le_sup (f := id)
      (Finset.mem_image_of_mem _ (hs.mem_toFinset.2 hi))

/-- The inclusion of an open and closed subscheme is quasi-compact. -/
lemma Scheme.Opens.quasiCompact_ι_of_isClosed {X : Scheme.{u}} (W : X.Opens)
    (hW : IsClosed (W : Set X)) : QuasiCompact W.ι :=
  ⟨fun _ _ hc ↦ hW.isClosedEmbedding_subtypeVal.isCompact_preimage hc⟩

end AlgebraicGeometry
