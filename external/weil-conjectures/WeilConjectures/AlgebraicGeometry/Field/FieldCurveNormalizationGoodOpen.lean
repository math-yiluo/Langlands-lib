/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.Thickening
import WeilConjectures.AlgebraicGeometry.DenseOpenComponentModifications
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# A dense thickening locus for componentwise normalization

Source: Stacks Project, Tag 0GK7, last paragraph, using Tags 0BXR and 035Q.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

private theorem generic_mem_dense_open {A : Type*} [TopologicalSpace A]
    (hA : (irreducibleComponents A).Finite) {W : Set A} (hW : Dense W)
    (hWo : IsOpen W) {x : A} (hx : closure {x} ∈ irreducibleComponents A) : x ∈ W := by
  have he := closure_sUnion_irreducibleComponents_sdiff_singleton hA _ hx
  have hopen : IsOpen (⋃₀ (irreducibleComponents A \ {closure {x}}))ᶜ := by
    rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
    exact hA.sdiff.isClosed_biUnion fun C hC ↦ isClosed_of_mem_irreducibleComponents C hC.1
  have hne : (⋃₀ (irreducibleComponents A \ {closure {x}}))ᶜ.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, closure_empty] at he
    exact (Set.singleton_nonempty x).ne_empty (Set.subset_empty_iff.mp (he ▸ subset_closure))
  obtain ⟨y, hy, hyW⟩ := hW.inter_open_nonempty _ hopen hne
  have hxy : x ⤳ y := by
    rw [specializes_iff_mem_closure, ← he]
    exact subset_closure hy
  exact hxy.mem_open hWo hyW

set_option backward.isDefEq.respectTransparency false in
/-- The normalization of the reduced irreducible components of an algebraic scheme is
finite and surjective, and is a thickening over a dense open of the target. The inverse
image of that open is dense in each normalized component.

Source: Stacks Project, Tag 0GK7, last paragraph; Varieties, Tag 0BXR.
(blueprint: lem-weil-pbc-field-curve-normalization-good-open)

Proof: Factor each integral component through the reduction. The reduction is a
homeomorphism, so these maps still enumerate its distinct irreducible components.
Each component normalization is finite and is an isomorphism on a dense open.
The dense-open component-modifications lemma gives a dense open in the reduction
where their coproduct is an isomorphism. Transport that open through the reduction
homeomorphism. Over it the original map is the composite of an isomorphism and a
surjective closed immersion. Finiteness follows componentwise. Surjectivity follows
from the component cover and surjectivity of normalization. Finally every normalized
component maps openly onto its component on the isomorphism locus, so the inverse
image of the chosen dense open is a nonempty open in an integral scheme, hence dense.
-/
theorem field_curve_normalization_good_open
    {k : Type u} [Field k] (X : Scheme.{u}) (q : X ⟶ Spec (.of k))
    [LocallyOfFiniteType q] (n : ℕ) (C Y : Fin n → Scheme.{u})
    (hC : ∀ i, IsIntegral (C i)) (c : ∀ i, C i ⟶ X)
    (e : ∀ i, Y i ≅ @Scheme.normalization (C i) (hC i))
    (hc : ∀ i, IsClosedImmersion (c i) ∧ Set.range (c i) ∈ irreducibleComponents X)
    (hinj : Function.Injective (fun i ↦ Set.range (c i)))
    (hcover : ∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (c i) = Z) :
    let ν := Sigma.desc (fun i ↦ (e i).hom ≫
      @Scheme.fromNormalization (C i) (hC i) ≫ c i)
    IsFinite ν ∧ Surjective ν ∧
      ∃ W : X.Opens, Dense (W : Set X) ∧
        (∀ i, Dense (((e i).hom ≫ @Scheme.fromNormalization (C i) (hC i) ≫ c i) ⁻¹'
          (W : Set X))) ∧ IsThickening (pullback.snd ν W.ι) := by
  classical
  let (i : Fin n) : IsIntegral (C i) := hC i
  let (i : Fin n) : IsClosedImmersion (c i) := (hc i).1
  let R := X.nilradical.subscheme
  let r := X.nilradical.subschemeι
  have hr : Surjective r :=
    (reduction_isReduced_isClosedImmersion_isSurjective_isUniversalHomeomorphism X).2.2.1
  have : Surjective r := hr
  have hrh : IsHomeomorph r :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨r.isEmbedding, r.surjective⟩
  let cR (i : Fin n) : C i ⟶ R := (c i).liftNilradical
  have hcR (i : Fin n) : cR i ≫ r = c i := (c i).liftNilradical_subschemeι
  have hcrange (i : Fin n) : Set.range (cR i) = r ⁻¹' Set.range (c i) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (congrArg (fun f : C i ⟶ X ↦ f y) (hcR i)).symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hrh.injective ((congrArg (fun f : C i ⟶ X ↦ f y) (hcR i)).trans hy)⟩
  have hcRcomp (i : Fin n) : IsIntegral (C i) ∧ IsClosedImmersion (cR i) ∧
      Set.range (cR i) ∈ irreducibleComponents R := by
    refine ⟨inferInstance, ?_, ?_⟩
    · have : IsClosedImmersion (cR i ≫ r) := hcR i ▸ inferInstance
      exact IsClosedImmersion.of_comp (cR i) r
    · rw [hcrange]
      apply preimage_mem_irreducibleComponents (hc i).2 hrh.isOpenEmbedding
      simpa only [hrh.surjective.range_eq, Set.inter_univ] using (hc i).2.1.1
  have hRinj : Function.Injective (fun i ↦ Set.range (cR i)) := by
    intro i j hij
    apply hinj
    have := congrArg (fun s : Set R ↦ r '' s) hij
    simpa only [hcrange, Set.image_preimage_eq _ hrh.surjective] using this
  have hRcover : ∀ Z ∈ irreducibleComponents R, ∃ i, Set.range (cR i) = Z := by
    intro Z hZ
    have hz := image_mem_irreducibleComponents_of_isPreirreducible_fiber r
      hrh.continuous hrh.isOpenMap
      (fun x ↦ (Set.subsingleton_singleton.preimage hrh.injective).isPreirreducible)
      hrh.surjective hZ
    obtain ⟨i, hi⟩ := hcover _ hz
    refine ⟨i, ?_⟩
    rw [hcrange, hi, Set.preimage_image_eq _ hrh.injective]
  let a (i : Fin n) := (e i).hom ≫ (C i).fromNormalization
  have ha (i : Fin n) : ∃ U : (C i).Opens, Dense (U : Set (C i)) ∧ IsIso (a i ∣_ U) := by
    obtain ⟨U, hU, hUi⟩ := (C i).exists_isIso_fromNormalization_restrict (c i ≫ q)
    have : IsIso ((C i).fromNormalization ∣_ U) := hUi
    refine ⟨U, U.isOpen.dense hU, ?_⟩
    dsimp [a]
    rw [morphismRestrict_comp]
    infer_instance
  obtain ⟨U, hUd, hUi⟩ := exists_dense_open_isIso_component_modifications R n C cR
    hcRcomp hRinj hRcover Y a ha
  let νR := Sigma.desc (fun i ↦ a i ≫ cR i)
  let ν := Sigma.desc (fun i ↦ (e i).hom ≫ (C i).fromNormalization ≫ c i)
  have hν : ν = νR ≫ r := by
    apply Sigma.hom_ext
    intro i
    simp [ν, νR, a, hcR]
  have hfin (i : Fin n) : IsFinite ((e i).hom ≫ (C i).fromNormalization ≫ c i) := by
    have := (C i).isFinite_fromNormalization_of_locallyOfFiniteType (c i ≫ q)
    infer_instance
  have hνfin : IsFinite ν := by
    dsimp [ν]
    exact IsFinite.sigmaDesc _
  have hνsurj : Surjective ν := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨i, hi⟩ := hcover (irreducibleComponent x)
      (irreducibleComponent_mem_irreducibleComponents x)
    obtain ⟨y, hy⟩ := hi.symm ▸ mem_irreducibleComponent (x := x)
    obtain ⟨z, hz⟩ := (C i).fromNormalization.surjective y
    refine ⟨(Sigma.ι Y i) ((e i).inv z), ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    simpa using (congrArg (c i) hz).trans hy
  let W : X.Opens := ⟨r '' (U : Set R), hrh.isOpenMap _ U.isOpen⟩
  have hWU : r ⁻¹ᵁ W = U := by
    ext x
    exact hrh.injective.mem_set_image
  have hWi : IsClosedImmersion (ν ∣_ W) := by
    have : IsIso (νR ∣_ (r ⁻¹ᵁ W)) := hWU.symm ▸ hUi
    rw [hν, morphismRestrict_comp]
    infer_instance
  have hWd : Dense (W : Set X) :=
    hrh.surjective.denseRange.dense_image hrh.continuous hUd
  refine ⟨hνfin, hνsurj, W, hWd, ?_, ?_⟩
  · intro i
    have : IsIntegral (Y i) := IsIntegral.of_isIso (e i).inv
    apply (W.isOpen.preimage
      ((e i).hom ≫ (C i).fromNormalization ≫ c i).continuous).dense
    have hXfin : (irreducibleComponents X).Finite :=
      (Set.finite_range (fun i ↦ Set.range (c i))).subset (by
        intro Z hZ
        obtain ⟨i, hi⟩ := hcover Z hZ
        exact ⟨i, hi⟩)
    have hg := (genericPoint_spec (C i)).image (c i).continuous
    have hgc : closure {(c i) (genericPoint (C i))} = Set.range (c i) := by
      simpa only [Set.image_univ, (c i).isClosedEmbedding.isClosed_range.closure_eq]
        using hg.def
    have hxW := generic_mem_dense_open hXfin hWd W.isOpen (hgc.symm ▸ (hc i).2)
    obtain ⟨z, hz⟩ := (C i).fromNormalization.surjective (genericPoint (C i))
    refine ⟨(e i).inv z, ?_⟩
    change ((e i).hom ≫ (C i).fromNormalization ≫ c i) ((e i).inv z) ∈ (W : Set X)
    have hez : (e i).hom ((e i).inv z) = z := by
      rw [← Scheme.Hom.comp_apply, (e i).inv_hom_id]
      rfl
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hez, hz]
    exact hxW
  · have : Surjective ν := hνsurj
    have : IsClosedImmersion (pullback.snd ν W.ι) := by
      have : IsClosedImmersion (ν ∣_ W) := hWi
      rw [← (isPullback_morphismRestrict ν W).flip.isoPullback_inv_snd]
      infer_instance
    exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
