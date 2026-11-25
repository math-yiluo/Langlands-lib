/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.Topology.ConstructibleInConstructible

/-!
# Assembling stratifications of the pieces of a partition

Source: Stacks Project, Tag 03S0, final refinement in the proof, and Tag 09YJ
(blueprint: lem-weil-pbc-constructible-stratification-assembly).
-/

@[expose] public section

universe u

open CategoryTheory Topology

namespace AlgebraicGeometry.Scheme

/-- Stratify every member of a finite constructible immersed partition, then compose its
stratum immersions with the original immersion. Any predicate true of these composite
maps holds on the assembled stratification.

Source: Stacks Project, Tag 03S0, final refinement in the proof; constructibility is
Stacks Tag 09YJ (blueprint: lem-weil-pbc-constructible-stratification-assembly).

Proof:
1. Index the new pieces by the finite dependent sum of the indices of the local
   stratifications, and reindex this sum by `Fin` of its cardinality. Use exactly their
   domain schemes, with immersion the composite of the two given immersions.
2. Composition of immersions is an immersion. Its image is the image of the local
   stratum under the outer immersion and is locally closed. An immersion identifies
   its source homeomorphically with its image. Each local stratum is constructible in
   that image, and the image is constructible in X; Tag 09YJ makes the composite image
   constructible in X, whose affine opens form a basis of quasi-compact opens.
3. These images cover X because the outer pieces cover X and each local stratification
   covers its source. Two images in different outer pieces are disjoint by the outer
   partition; in the same piece they are disjoint by injectivity of its immersion and
   the local partition. These data define a Stratification of X.
4. The predicate on every new immersion is precisely the corresponding given proof,
   since we used the local domain and the composite immersion without replacement.
   Empty outer partitions and empty local partitions use the empty dependent sum. -/
theorem exists_stratification_of_stratified_partition
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (n : ℕ) (Y : Fin n → Scheme.{u}) (ι : ∀ i, Y i ⟶ X)
    (hι : ∀ i, IsImmersion (ι i))
    (hc : ∀ i, Topology.IsConstructible (Set.range (ι i)))
    (hd : Pairwise (fun i k ↦ Disjoint (Set.range (ι i)) (Set.range (ι k))))
    (hu : (⋃ i, Set.range (ι i)) = Set.univ)
    (T : ∀ i, Stratification (Y i))
    (P : ∀ Z : Scheme.{u}, (Z ⟶ X) → Prop)
    (hP : ∀ i b, P ((T i).domain b) ((T i).immersion b ≫ ι i)) :
    ∃ R : Stratification X,
      (∀ k, Topology.IsConstructible (R.stratum k)) ∧
      ∀ k, P (R.domain k) (R.immersion k) := by
  classical
  have hi (i : Fin n) : IsImmersion (ι i) := hι i
  have ht (i : Fin n) (b : Fin (T i).n) : IsImmersion ((T i).immersion b) :=
    (T i).isImmersion b
  let K := (i : Fin n) × Fin (T i).n
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let f (k : K) := (T k.1).immersion k.2 ≫ ι k.1
  have hcon (k : K) : IsConstructible (Set.range (f k)) := by
    let g : Y k.1 ≃ₜ Set.range (ι k.1) := (ι k.1).isEmbedding.toHomeomorph
    apply isConstructible_of_isConstructible_subspace
      PrespectralSpace.isTopologicalBasis (hc k.1)
      (by
        rintro x ⟨z, rfl⟩
        exact ⟨(T k.1).immersion k.2 z, rfl⟩)
    have h := ((T k.1).isConstructible_stratum k.2).image_of_isOpenEmbedding
      g.isOpenEmbedding (by simp)
    convert h using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨(T k.1).immersion k.2 z, ?_, ?_⟩
      · rw [← (T k.1).range_immersion]
        exact Set.mem_range_self z
      · apply Subtype.ext
        exact hz
    · rintro ⟨z, hz, hx⟩
      rw [← (T k.1).range_immersion] at hz
      obtain ⟨w, rfl⟩ := hz
      exact ⟨w, congrArg Subtype.val hx⟩
  have hdis : Pairwise (fun k l : K ↦ Disjoint (Set.range (f k)) (Set.range (f l))) := by
    rintro ⟨i, b⟩ ⟨i', b'⟩ hkl
    by_cases hij : i = i'
    · subst i'
      have hbb : b ≠ b' := fun h ↦ hkl (by cases h; rfl)
      apply Set.disjoint_left.mpr
      rintro x ⟨z, hz⟩ ⟨w, hw⟩
      have heq : (T i).immersion b z = (T i).immersion b' w :=
        (ι i).isEmbedding.injective (hz.trans hw.symm)
      exact Set.disjoint_left.mp ((T i).pairwise_disjoint_stratum hbb)
        (by rw [← (T i).range_immersion]; exact Set.mem_range_self z)
        (by rw [← (T i).range_immersion]; exact ⟨w, heq.symm⟩)
    · exact (hd hij).mono
        (by rintro x ⟨z, rfl⟩; exact Set.mem_range_self _)
        (by rintro x ⟨z, rfl⟩; exact Set.mem_range_self _)
  let R : Stratification X := {
    n := Fintype.card K
    stratum := fun k ↦ Set.range (f (e k))
    isLocallyClosed_stratum := fun k ↦ (f (e k)).isLocallyClosed_range
    isConstructible_stratum := fun k ↦ hcon (e k)
    iUnion_stratum_eq_univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.mp (hu.symm ▸ Set.mem_univ x)
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp
        ((T i).iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y)
      rw [← (T i).range_immersion] at hb
      obtain ⟨z, rfl⟩ := hb
      refine Set.mem_iUnion.mpr ⟨e.symm ⟨i, b⟩, ?_⟩
      rw [e.apply_symm_apply]
      exact ⟨z, rfl⟩
    pairwise_disjoint_stratum := fun k l hkl ↦ hdis (e.injective.ne hkl)
    domain := fun k ↦ (T (e k).1).domain (e k).2
    immersion := fun k ↦ f (e k)
    isImmersion := fun k ↦ inferInstance
    range_immersion := fun k ↦ rfl }
  exact ⟨R, R.isConstructible_stratum, fun k ↦ hP (e k).1 (e k).2⟩

end AlgebraicGeometry.Scheme
