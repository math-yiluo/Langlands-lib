/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Refinement

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

private theorem irreducible_partition (Y : Type u) [TopologicalSpace Y]
    [TopologicalSpace.NoetherianSpace Y] :
    ∃ T : Topology.Stratification Y, ∀ i, IsIrreducible (T.stratum i) := by
  classical
  let C := {Z : Set Y // Z ∈ irreducibleComponents Y}
  let : Fintype C :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y)).fintype
  let e : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  let Z (i : Fin (Fintype.card C)) : Set Y := (e i).1
  let B (i : Fin (Fintype.card C)) : Set Y := ⋃ j : {j // j < i}, Z j.1
  let P (i : Fin (Fintype.card C)) : Set Y := Z i \ B i
  have hZ (i) : Z i ∈ irreducibleComponents Y := (e i).2
  have hB (i) : IsClosed (B i) :=
    isClosed_iUnion_of_finite fun j ↦ isClosed_of_mem_irreducibleComponents _ (hZ j.1)
  have hirr (i) : IsIrreducible (P i) := by
    let o := (⋃₀ (irreducibleComponents Y \ {Z i}))ᶜ
    have ho : IsOpen o := by
      rw [isOpen_compl_iff, Set.sUnion_eq_biUnion]
      exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
        fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1
    have hcl : closure o = Z i :=
      closure_sUnion_irreducibleComponents_sdiff_singleton
        TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (Z i) (hZ i)
    have hsub : o ⊆ Z i := hcl ▸ subset_closure
    have hne : o.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty.mp h, closure_empty] at hcl
      exact (hZ i).1.nonempty.ne_empty hcl.symm
    have hoP : o ⊆ P i := by
      intro x hx
      refine ⟨hsub hx, ?_⟩
      intro hxB
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxB
      apply hx
      refine Set.mem_sUnion.mpr ⟨Z j.1, ⟨hZ j.1, ?_⟩, hj⟩
      simp only [Set.mem_singleton_iff]
      intro h
      have he : e j.1 = e i := Subtype.ext h
      exact (ne_of_lt j.2) (e.injective he)
    exact (hZ i).1.2.subset_irreducible hne ho hoP Set.sdiff_subset
  have hcover : ⋃ i, P i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hex : ∃ i, x ∈ Z i := by
      obtain ⟨z, hz, hx⟩ := Set.mem_sUnion.mp
        ((sUnion_irreducibleComponents (X := Y)).symm ▸ Set.mem_univ x)
      exact ⟨e.symm ⟨z, hz⟩, by simpa [Z] using hx⟩
    obtain ⟨i, hi, hmin⟩ := exists_minimal_of_wellFoundedLT (fun i ↦ x ∈ Z i) hex
    refine Set.mem_iUnion.mpr ⟨i, hi, ?_⟩
    rintro hxB
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxB
    exact (not_lt_of_ge (hmin hj (le_of_lt j.2))) j.2
  refine ⟨Topology.Stratification.ofNoetherianSpace (Fintype.card C) P
    (fun i ↦ (isClosed_of_mem_irreducibleComponents _ (hZ i)).isLocallyClosed.inter
      (hB i).isOpen_compl.isLocallyClosed) hcover ?_, hirr⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hxj.2 (Set.mem_iUnion.mpr ⟨⟨i, hlt⟩, hxi.1⟩)
  · exact hxi.2 (Set.mem_iUnion.mpr ⟨⟨j, hgt⟩, hxj.1⟩)

private theorem exists_immersion_locallyClosed (X : Scheme.{u}) (s : Set X)
    (hs : IsLocallyClosed s) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), IsImmersion f ∧ Set.range f = s := by
  classical
  let U : X.Opens := ⟨coborder s, hs.isOpen_coborder⟩
  let Z : TopologicalSpace.Closeds U.toScheme := ⟨Subtype.val ⁻¹' s, isClosed_preimage_val_coborder⟩
  let I := IdealSheafData.vanishingIdeal Z
  refine ⟨I.subscheme, I.subschemeι ≫ U.ι, inferInstance, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, I.range_subschemeι]
  change Subtype.val '' (Subtype.val ⁻¹' s) = s
  rw [Set.image_preimage_eq_inter_range, Subtype.range_coe]
  exact Set.inter_eq_left.mpr subset_coborder

private theorem exists_irreducible_stratification (Y : Scheme.{u})
    [TopologicalSpace.NoetherianSpace Y] :
    ∃ T : Stratification Y, ∀ i, IrreducibleSpace (T.domain i) := by
  classical
  obtain ⟨P, hP⟩ := irreducible_partition Y
  choose Z f hf hr using fun i ↦
    exists_immersion_locallyClosed Y (P.stratum i) (P.isLocallyClosed_stratum i)
  let T : Stratification Y := {
    toStratification := P
    domain := Z
    immersion := f
    isImmersion := hf
    range_immersion := hr }
  refine ⟨T, fun i ↦ ?_⟩
  have : IsImmersion (f i) := hf i
  have : IrreducibleSpace (Set.range (f i)) :=
    Subtype.irreducibleSpace ((hr i).symm ▸ hP i)
  exact (f i).isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr inferInstance

/-- A finite stratification of a Noetherian scheme admits an irreducible refinement.
Source: Stacks Project, Tags 0052 (1)-(3) and 0BA8; blueprint
`lem-weil-pbc-irreducible-refinement`.

Proof: each stratum, with its induced topology, is Noetherian. List its distinct
irreducible components C_1, ..., C_r, which are closed and cover the stratum, and set
P_j = C_j minus the union of the earlier components. This is open in C_j and locally
closed in the stratum. It is nonempty: otherwise irreducibility of C_j and finiteness
would force C_j to lie in an earlier component, contradicting maximality and distinctness.
Thus P_j is irreducible. The P_j are disjoint and cover the stratum, since each point
belongs to a first component. Omit empty original strata, which have no components.
Their images in X are locally closed, and hence constructible since X is Noetherian.
Realize each image by its reduced locally closed subscheme, whose underlying space is
homeomorphic to P_j. The finitely many pieces over all original strata give T; inclusion
of each piece in its original stratum proves T.Refines S. If X is empty, use n = 0.
(blueprint: lem-weil-pbc-irreducible-refinement-topological)
-/
theorem exists_irreducible_refinement_topological
    (X : Scheme.{u}) [IsNoetherian X] (S : Stratification X) :
    ∃ T : Stratification X,
      T.Refines S ∧ ∀ i : Fin T.n, IrreducibleSpace (T.domain i) := by
  classical
  have hN (i : Fin S.n) : TopologicalSpace.NoetherianSpace (S.domain i) :=
    (S.immersion i).isEmbedding.isInducing.noetherianSpace
  choose R hR using fun i ↦ exists_irreducible_stratification (S.domain i)
  let K := (i : Fin S.n) × Fin (R i).n
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let f (k : K) := (R k.1).immersion k.2 ≫ S.immersion k.1
  have hsub (k : K) : Set.range (f k) ⊆ S.stratum k.1 := by
    rintro x ⟨z, rfl⟩
    rw [← S.range_immersion]
    exact Set.mem_range_self _
  have hdis : Pairwise (fun k l : K ↦ Disjoint (Set.range (f k)) (Set.range (f l))) := by
    rintro ⟨i, b⟩ ⟨j, c⟩ hne
    by_cases hij : i = j
    · subst j
      have hbc : b ≠ c := fun h ↦ hne (by cases h; rfl)
      apply Set.disjoint_left.mpr
      rintro x ⟨z, hz⟩ ⟨w, hw⟩
      have heq : (R i).immersion b z = (R i).immersion c w :=
        (S.immersion i).isEmbedding.injective (hz.trans hw.symm)
      exact Set.disjoint_left.mp ((R i).pairwise_disjoint_stratum hbc)
        (by rw [← (R i).range_immersion]; exact Set.mem_range_self z)
        (by rw [← (R i).range_immersion]; exact ⟨w, heq.symm⟩)
    · exact (S.pairwise_disjoint_stratum hij).mono (hsub ⟨i, b⟩) (hsub ⟨j, c⟩)
  let T : Stratification X := {
    n := Fintype.card K
    stratum := fun k ↦ Set.range (f (e k))
    isLocallyClosed_stratum := fun k ↦ (f (e k)).isLocallyClosed_range
    isConstructible_stratum := fun k ↦
      (f (e k)).isLocallyClosed_range.isConstructible_of_noetherianSpace
    iUnion_stratum_eq_univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
        (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ x)
      rw [← S.range_immersion] at hi
      obtain ⟨y, rfl⟩ := hi
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp
        ((R i).iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y)
      rw [← (R i).range_immersion] at hb
      obtain ⟨z, rfl⟩ := hb
      refine Set.mem_iUnion.mpr ⟨e.symm ⟨i, b⟩, ?_⟩
      rw [e.apply_symm_apply]
      exact ⟨z, rfl⟩
    pairwise_disjoint_stratum := fun k l hkl ↦ hdis (e.injective.ne hkl)
    domain := fun k ↦ (R (e k).1).domain (e k).2
    immersion := fun k ↦ f (e k)
    isImmersion := fun k ↦ inferInstance
    range_immersion := fun k ↦ rfl }
  exact ⟨T, fun k ↦ ⟨(e k).1, hsub (e k)⟩, fun k ↦ hR (e k).1 (e k).2⟩

end AlgebraicGeometry.Scheme
