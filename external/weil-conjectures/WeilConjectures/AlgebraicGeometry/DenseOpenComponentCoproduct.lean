/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties

/-! # A component coproduct over prescribed dense opens -/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The component coproduct is an isomorphism on a dense open whose inverse image in
 each component lies in any prescribed dense open.
Source: Stacks Project, Morphisms, Tag 0BAJ, the reduction to disjoint components;
the explicit component-open argument of
`theorem-cohomology-curves`, steps 1 and 2.

Proof: Put Z i = range (ι i). Remove the union of the Z j for j ≠ i to get W i.
The union is closed because the family is finite. The generic point of Z i is
outside every other component by maximality and distinctness, so W i contains it.
The components cover X, hence W i is contained in Z i. The closed immersion ι i
restricted to W i is surjective onto a reduced scheme, and is therefore an
isomorphism: its ideal on each affine lies in the nilradical, which is zero.
Transfer V i intersected with the inverse image of W i across this isomorphism
and include the image as an open O i of X. A dense open of the integral C i
contains its generic point, so O i contains the generic point of Z i.
The O i are disjoint. Their union U is dense because its closure contains each
component, and the components cover X. The inverse image of U in C i is exactly
the inverse image of O i and lies in V i. The maps from these inverse images to
O i are isomorphisms; their coproduct is an isomorphism onto U, identified with
the restriction of Sigma.desc ι by base change of a scheme coproduct.
For an empty family the covering hypothesis forces X empty, and U is empty.
(blueprint: theorem-cohomology-curves) -/
theorem exists_dense_open_component_coproduct
    (X : Scheme.{u}) [IsReduced X]
    (n : ℕ) (C : Fin n → Scheme.{u}) (ι : ∀ i, C i ⟶ X)
    (hC : ∀ i, IsIntegral (C i) ∧ IsClosedImmersion (ι i) ∧
      Set.range (ι i) ∈ irreducibleComponents X)
    (hinj : Function.Injective (fun i ↦ Set.range (ι i)))
    (hcover : ∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (ι i) = Z)
    (V : ∀ i, (C i).Opens) (hV : ∀ i, Dense (V i : Set (C i))) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsIso (CategoryTheory.Limits.Sigma.desc ι ∣_ U) ∧
      ∀ i, ι i ⁻¹ᵁ U ≤ V i := by
  classical
  have hclosed : ∀ i, IsClosedImmersion (ι i) := fun i ↦ (hC i).2.1
  have hfinite : (irreducibleComponents X).Finite := by
    have heq : irreducibleComponents X = Set.range (fun i ↦ Set.range (ι i)) := by
      ext Z
      exact ⟨fun h ↦ hcover Z h, fun ⟨i, hi⟩ ↦ hi ▸ (hC i).2.2⟩
    rw [heq]
    exact Set.finite_range _
  let W : Fin n → X.Opens := fun i ↦
    ⟨(⋃₀ (irreducibleComponents X \ {Set.range (ι i)}))ᶜ, by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact hfinite.sdiff.isClosed_biUnion
        (fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1)⟩
  have hWcl (i) : closure (W i : Set X) = Set.range (ι i) :=
    closure_sUnion_irreducibleComponents_sdiff_singleton hfinite _ (hC i).2.2
  have hWsub (i) : (W i : Set X) ⊆ Set.range (ι i) := by
    rw [← hWcl i]
    exact subset_closure
  have hWne (i) : (W i : Set X).Nonempty := by
    by_contra! h
    have hempty : Set.range (ι i) = ∅ := by rw [← hWcl i, h, closure_empty]
    exact (hC i).2.2.1.nonempty.ne_empty hempty
  have hWiso (i) : IsIso (ι i ∣_ W i) := by
    have : Surjective (ι i ∣_ W i) := ⟨by
      intro x
      obtain ⟨y, hy⟩ := hWsub i x.2
      refine ⟨⟨y, ?_⟩, ?_⟩
      · change ι i y ∈ W i
        simp [hy, x.2]
      · apply Subtype.ext
        simpa [morphismRestrict_base_coe] using hy⟩
    exact isIso_of_isClosedImmersion_of_surjective _
  let T (i) : (ι i ⁻¹ᵁ W i).toScheme.Opens := (ι i ⁻¹ᵁ W i).ι ⁻¹ᵁ V i
  let O (i) : X.Opens := (W i).ι ''ᵁ ((ι i ∣_ W i) ''ᵁ T i)
  have hOsub (i) : O i ≤ W i := (W i).ι_image_le _
  have hOimage (i) : (O i : Set X) = ι i ''
      ((V i : Set (C i)) ∩ (ι i ⁻¹ᵁ W i : Set (C i))) := by
    ext x
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y.1, ⟨hy, y.2⟩, (morphismRestrict_base_coe _ _ _).symm⟩
    · rintro ⟨y, ⟨hyV, hyW⟩, rfl⟩
      exact ⟨(ι i ∣_ W i) ⟨y, hyW⟩,
        ⟨⟨y, hyW⟩, hyV, rfl⟩, morphismRestrict_base_coe _ _ _⟩
  have hOne (i) : (O i : Set X).Nonempty := by
    have hpre : (ι i ⁻¹ᵁ W i : Set (C i)).Nonempty := by
      obtain ⟨x, hx⟩ := hWne i
      obtain ⟨y, rfl⟩ := hWsub i hx
      exact ⟨y, hx⟩
    rw [hOimage i]
    simpa only [Set.inter_comm] using
      (hV i |>.inter_open_nonempty _ (ι i ⁻¹ᵁ W i).isOpen hpre).image (ι i)
  have hOcl (i) : closure (O i : Set X) = Set.range (ι i) := by
    have hsub : (O i : Set X) ⊆ Set.range (ι i) :=
      fun x hx ↦ hWsub i (hOsub i hx)
    apply Set.Subset.antisymm
    · exact closure_minimal hsub (ι i).isClosedEmbedding.isClosed_range
    · have h := subset_closure_inter_of_isPreirreducible_of_isOpen
        (hC i).2.2.1.2 (O i).isOpen
        (by simpa only [Set.inter_eq_right.mpr hsub] using hOne i)
      simpa only [Set.inter_eq_right.mpr hsub] using h
  have hOdisj : Pairwise (fun i j ↦ Disjoint (O i : Set X) (O j : Set X)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact hOsub i hxi (Set.mem_sUnion_of_mem (hWsub j (hOsub j hxj))
      ⟨(hC j).2.2, by
        simpa only [Set.mem_singleton_iff] using
          (show Set.range (ι j) ≠ Set.range (ι i) from fun h ↦ hij (hinj h).symm)⟩)
  have hOV (i) : ι i ⁻¹ᵁ O i ≤ V i := by
    intro y hy
    change ι i y ∈ (O i : Set X) at hy
    rw [hOimage i] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have heq : z = y := (ι i).isClosedEmbedding.injective hzy
    exact heq ▸ hz.1
  have hOiso (i) : IsIso (ι i ∣_ O i) := by
    have h := IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
      (hWiso i) ((W i).ι ⁻¹ᵁ O i)
    have h' := (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
      (morphismRestrictRestrict (ι i) (W i) ((W i).ι ⁻¹ᵁ O i))).mp h
    change IsIso (ι i ∣_ (W i).ι ''ᵁ ((W i).ι ⁻¹ᵁ O i)) at h'
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, inf_eq_right.mpr (hOsub i)] at h'
  let U : X.Opens := ⨆ i, O i
  have hOU (i) : O i ≤ U := le_iSup O i
  have hUdense : Dense (U : Set X) := by
    intro x
    obtain ⟨i, hi⟩ := hcover (irreducibleComponent x)
      (irreducibleComponent_mem_irreducibleComponents x)
    have hx : x ∈ closure (O i : Set X) := by
      rw [hOcl i, hi]
      exact mem_irreducibleComponent
    exact closure_mono (hOU i) hx
  have hpre (i) : ι i ⁻¹ᵁ U = ι i ⁻¹ᵁ O i := by
    apply le_antisymm
    · intro y hy
      change ι i y ∈ (U : Set X) at hy
      have hy' : ι i y ∈ ⋃ j, (O j : Set X) := by
        simpa only [U, TopologicalSpace.Opens.coe_iSup] using hy
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy'
      by_cases hij : i = j
      · subst j; exact hj
      · exact False.elim (hOsub j hj (Set.mem_sUnion_of_mem (t := Set.range (ι i)) ⟨y, rfl⟩
          ⟨(hC i).2.2, by
            simpa only [Set.mem_singleton_iff] using
              (show Set.range (ι i) ≠ Set.range (ι j) from fun h ↦ hij (hinj h))⟩))
    · exact (ι i).preimage_mono (hOU i)
  refine ⟨U, hUdense, ?_, fun i ↦ (hpre i).le.trans (hOV i)⟩
  let a (i : Fin n) : (ι i ⁻¹ᵁ U).toScheme ⟶
      (Limits.Sigma.desc ι ⁻¹ᵁ U).toScheme :=
    (Limits.Sigma.ι C i).resLE _ _ (by
      rw [← Scheme.Hom.comp_preimage, Limits.Sigma.ι_comp_desc])
  have ha : IsIso (Limits.Sigma.desc a) := by
    have hau := FinitaryPreExtensive.isUniversal_finiteCoproducts
      (Limits.coproductIsCoproduct C)
    have hc : Nonempty (Limits.IsColimit (Limits.Cofan.mk _ a)) := by
      apply hau (Limits.Cofan.mk _ a)
        (Discrete.natTrans fun i ↦ (ι i.as ⁻¹ᵁ U).ι) (Limits.Sigma.desc ι ⁻¹ᵁ U).ι
      · ext i
        simp [a]
      · exact NatTrans.Equifibered.of_discrete _
      · intro i
        change IsPullback (a i.as) (ι i.as ⁻¹ᵁ U).ι
          (Limits.Sigma.desc ι ⁻¹ᵁ U).ι (Limits.Sigma.ι C i.as)
        apply IsOpenImmersion.isPullback
        · simp [a]
        · simp [← Scheme.Hom.comp_preimage]
    exact (Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mp hc
  let b (i : Fin n) : (ι i ⁻¹ᵁ U).toScheme ⟶ U.toScheme :=
    ι i ∣_ U
  have hbopen (i) : IsOpenImmersion (b i) := by
    have heq : b i = (C i).homOfLE (hpre i).le ≫ (ι i ∣_ O i) ≫
        X.homOfLE (hOU i) := by
      apply (cancel_mono U.ι).mp
      simp [b]
    rw [heq]
    infer_instance
  have hbrange (i) : (b i).opensRange = U.ι ⁻¹ᵁ O i := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change ((b i) y).1 ∈ O i
      rw [show ((b i) y).1 = ι i y.1 from morphismRestrict_base_coe _ _ _]
      exact (hpre i).le y.2
    · intro hx
      have hxO : x.1 ∈ O i := hx
      have hxrange : x.1 ∈ Set.range (ι i) := hWsub i (hOsub i hxO)
      obtain ⟨y, hy⟩ := hxrange
      refine ⟨⟨y, ?_⟩, ?_⟩
      · change ι i y ∈ U
        simp [hy, x.2]
      · apply Subtype.ext
        simpa [b, morphismRestrict_base_coe] using hy
  have hbiso : IsIso (Limits.Sigma.desc b) := by
    apply (Limits.Cofan.nonempty_isColimit_iff_isIso_sigmaDesc
      (Limits.Cofan.mk U.toScheme b)).mp
    apply nonempty_isColimit_cofanMk_of
    · simp_rw [hbrange, ← Scheme.Hom.preimage_iSup]
      change U.ι ⁻¹ᵁ U = ⊤
      exact U.ι_preimage_self
    · intro i j hij
      change Disjoint (b i).opensRange (b j).opensRange
      rw [hbrange, hbrange]
      exact disjoint_iff.mpr (by
        ext x
        exact ⟨fun h ↦ False.elim (Set.disjoint_left.mp (hOdisj hij) h.1 h.2),
          fun h ↦ False.elim h⟩)
  have hfac : Limits.Sigma.desc a ≫ Limits.Sigma.desc ι ∣_ U =
      Limits.Sigma.desc b := by
    apply Limits.Sigma.hom_ext
    intro i
    apply (cancel_mono U.ι).mp
    simp [a, b]
  have : IsIso (Limits.Sigma.desc a ≫ Limits.Sigma.desc ι ∣_ U) := by
    rw [hfac]
    exact hbiso
  exact (isIso_comp_left_iff (Limits.Sigma.desc a) (Limits.Sigma.desc ι ∣_ U)).mp this

end AlgebraicGeometry
