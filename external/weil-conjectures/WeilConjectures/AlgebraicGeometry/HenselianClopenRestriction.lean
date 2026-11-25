/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.Henselian

import WeilConjectures.Topology.SpectralClosedClopenDecompositionLift
import WeilConjectures.AlgebraicGeometry.HenselianConnectedness

/-!
# Clopen restriction to a proper henselian closed fibre

Source: Stacks Project, Tags 0A0B (Stein connectedness) and 0CAM (clopen lifting).
(blueprint: lem-weil-pbc-henselian-clopen-restriction)
-/

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Restriction to the closed fibre is injective and surjective on clopen subsets.
Source: Stacks Project, Etale Cohomology, Lemma 59.91.1, Tag 0A0B.
(blueprint: lem-weil-pbc-henselian-clopen-restriction)

Proof: The quotient spectrum morphism is a closed immersion, and so is its base change
`i`. The pullback range formula identifies its image `Z` with `f⁻¹(V(I))`. Stein
connectedness for the proper henselian morphism says that `Y` is spectral and that
`Z` meets every irreducible closed subset in a nonempty connected set.

For uniqueness, if two clopens have equal inverse images but differ, one of their
closed differences is nonempty. The closure of a point in that difference is contained
in it and meets `Z`, contradicting equality of the inverse images.

For existence, the closed embedding identifies `Y₀` homeomorphically with `Z`.
Transport the given clopen and its complement across this homeomorphism. Each point
closure meets `Z` in a connected set, so Tag 0CAM lifts this closed decomposition to
a decomposition `Y = U ∐ W` into closed sets. Since `U = Wᶜ`, the set `U` is also open.
The intersection identity for the lifted decomposition, together with injectivity
of `i`, gives `i⁻¹(U) = V`. Empty spaces and empty pieces are included by the same
argument; no nonemptiness of `Y` or of the prescribed clopen is required. -/
theorem Scheme.henselian_clopen_restriction
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ Spec (.of A)) [IsProper f] (i : Y₀ ⟶ Y)
    (f₀ : Y₀ ⟶ Spec (.of (A ⧸ I)))
    (h : IsPullback i f₀ f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :
    (∀ U V : Set Y, IsOpen U ∧ IsClosed U → IsOpen V ∧ IsClosed V →
      i.base ⁻¹' U = i.base ⁻¹' V → U = V) ∧
    (∀ V : Set Y₀, IsOpen V ∧ IsClosed V →
      ∃ U : Set Y, (IsOpen U ∧ IsClosed U) ∧ i.base ⁻¹' U = V) := by
  classical
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have : IsClosedImmersion i :=
    MorphismProperty.of_isPullback h.flip (IsClosedImmersion.spec_of_quotient_mk (R := .of A) I)
  have hrange : Set.range i = f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    have hi : h.isoPullback.hom ≫ pullback.fst f q = i := h.isoPullback_hom_fst
    rw [← hi, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr h.isoPullback.hom.surjective, Set.image_univ,
      Scheme.Pullback.range_fst]
    change f ⁻¹' Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    simp only [Ideal.mk_ker]
  obtain ⟨hspectral, _, hconnected⟩ :=
    f.spectralSpace_and_isClosed_and_isConnected_inter I
  have : SpectralSpace Y := hspectral
  have hmeet (C : Set Y) (hC : IsClosed C) (hne : C.Nonempty) :
      (C ∩ Set.range i).Nonempty := by
    rw [hrange]
    obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, hz⟩ :=
      (hconnected _ isClosed_closure isIrreducible_singleton.closure).nonempty
    exact ⟨y, (closure_minimal (Set.singleton_subset_iff.mpr hx) hC) hy, hz⟩
  constructor
  · intro U V hU hV heq
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hxV
      obtain ⟨y, hy, z, rfl⟩ := hmeet (U \ V) (hU.2.sdiff hV.1) ⟨x, hx, hxV⟩
      have hz : z ∈ i.base ⁻¹' U := hy.1
      rw [heq] at hz
      exact hy.2 hz
    · intro x hx
      by_contra hxU
      obtain ⟨y, hy, z, rfl⟩ := hmeet (V \ U) (hV.2.sdiff hU.1) ⟨x, hx, hxU⟩
      have hz : z ∈ i.base ⁻¹' V := hy.1
      rw [← heq] at hz
      exact hy.2 hz
  · intro V hV
    let Z : Set Y := Set.range i
    let e : Y₀ ≃ₜ Z := i.isClosedEmbedding.isEmbedding.toHomeomorph
    have hZ : IsClosed Z := i.isClosedEmbedding.isClosed_range
    have hc (x : Y) : ConnectedSpace (↥(Z ∩ closure ({x} : Set Y))) := by
      apply isConnected_iff_connectedSpace.mp
      rw [Set.inter_comm]
      change IsConnected (closure ({x} : Set Y) ∩ Set.range i)
      rw [hrange]
      exact hconnected _ isClosed_closure isIrreducible_singleton.closure
    let V₁ : Set Z := e '' V
    have hV₁ : IsClosed V₁ := e.isClosedMap _ hV.2
    have hV₂ : IsClosed V₁ᶜ := (e.isOpenMap _ hV.1).isClosed_compl
    obtain ⟨U, W, hU, hW, hd, hu, h₁, _⟩ :=
      TopCat.spectral_closed_clopen_decomposition_lift Y Z hZ hc V₁ V₁ᶜ
        hV₁ hV₂ (Set.union_compl_self _) disjoint_compl_right
    have hUW : U = Wᶜ := by
      ext x
      have hcover : x ∈ U ∪ W := hu.symm ▸ Set.mem_univ x
      have hdisj := Set.disjoint_left.mp hd
      simp only [Set.mem_union, Set.mem_compl_iff] at hcover ⊢
      tauto
    refine ⟨U, ⟨hUW ▸ hW.isOpen_compl, hU⟩, ?_⟩
    ext x
    change i x ∈ U ↔ x ∈ V
    have hxZ : i x ∈ Z := ⟨x, rfl⟩
    have he : (e x : Y) = i x := rfl
    have hmem : i x ∈ Subtype.val '' V₁ ↔ i x ∈ U := by
      rw [h₁]
      exact and_iff_right hxZ
    rw [← hmem]
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, hz⟩
      have hxy : y = x := i.isClosedEmbedding.injective hz
      simpa [hxy] using hy
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, he⟩

end AlgebraicGeometry
