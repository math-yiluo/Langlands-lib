/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Topology.Constructible
import WeilConjectures.Topology.ConstructibleIsRetrocompact

/-!
# An affine neighborhood on which the selected constructible stratum is closed

Source: Stacks Project, Topology, Tags 004E, 005J and 09YH; Schemes, Tag 01IT
(auxiliary; not a blueprint node).
-/

@[expose] public section


universe u

namespace AlgebraicGeometry

/-- A selected stratum of a finite locally closed constructible partition is closed on
an affine neighborhood of any of its points. Every stratum restricts to a locally closed
constructible subset there, and the selected stratum has quasi-compact open complement.
Source: Stacks Project, Topology, Tags 004E, 005J and 09YH; Schemes, Tag 01IT
(auxiliary; not a blueprint node).

Proof:
1. Write `S k = W ∩ Z` with `W` open and `Z` closed, using
   `def-weil-locally-closed-subset`. Since `y ∈ W`, choose an affine open neighborhood
   `V ⊆ W` by `lem-weil-pbc-affine-opens-basis`. The selected stratum restricts to
   `Z ∩ V`, which is closed in `V`.
2. Restrict the open/closed presentation of each `S i` to `V` to obtain local closedness.
   Apply `lem-weil-pbc-constructible-open-restriction` (Tag 005J) to obtain constructibility
   in the subspace `V`.
3. By `def-weil-constructible-subset`, the complement of the selected restricted stratum
   is constructible. It is open by step 1. The affine scheme `V` is quasi-compact by
   `lem-weil-pbc-affine-scheme-qcqs`. Apply `lem-weil-pbc-constructible-is-retrocompact`
   (Tag 09YH) with the whole space of `V` as quasi-compact open test subset; its
   intersection with this complement is the complement itself, hence is quasi-compact. -/
theorem exists_affineOpen_closed_stratum (Y : Scheme.{u}) (N : ℕ)
    (S : Fin N → Set Y) (hcover : (⋃ i, S i) = Set.univ)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (S i) (S j)))
    (hlocallyClosed : ∀ i, IsLocallyClosed (S i))
    (hconstructible : ∀ i, Topology.IsConstructible (S i))
    (y : Y) (k : Fin N) (hy : y ∈ S k) :
    ∃ V : Y.Opens, IsAffineOpen V ∧ y ∈ V ∧
      IsClosed (Subtype.val ⁻¹' S k : Set V) ∧
      (∀ i, IsLocallyClosed (Subtype.val ⁻¹' S i : Set V) ∧
        Topology.IsConstructible (Subtype.val ⁻¹' S i : Set V)) ∧
      IsCompact ((Subtype.val ⁻¹' S k : Set V)ᶜ) := by
  classical
  have _hcover_used := hcover
  have _hdisjoint_used := hdisjoint
  obtain ⟨W, Z, hW, hZ, hSk⟩ := hlocallyClosed k
  let Wop : Y.Opens := ⟨W, hW⟩
  have hyW : y ∈ Wop := by
    rw [hSk] at hy
    exact hy.1
  obtain ⟨V, hVaff, hyV, hVW⟩ :=
    exists_isAffineOpen_mem_and_subset hyW
  refine ⟨V, hVaff, hyV, ?_, ?_, ?_⟩
  · have hpre : (Subtype.val ⁻¹' S k : Set V) =
        (Subtype.val ⁻¹' Z : Set V) := by
      ext x
      constructor
      · intro hx
        exact (hSk ▸ hx).2
      · intro hx
        have hxW : (x.1 : Y) ∈ W := hVW x.property
        exact hSk ▸ ⟨hxW, hx⟩
    rw [hpre]
    exact hZ.preimage continuous_subtype_val
  · intro i
    constructor
    · exact (hlocallyClosed i).preimage continuous_subtype_val
    · exact (hconstructible i).preimage_of_isOpenEmbedding
        V.2.isOpenEmbedding_subtypeVal
  · have hC : Topology.IsConstructible
        ((Subtype.val ⁻¹' S k : Set V)ᶜ) := by
      rw [← Set.preimage_compl]
      exact (hconstructible k).compl.preimage_of_isOpenEmbedding
        V.2.isOpenEmbedding_subtypeVal
    exact @IsRetrocompact.isCompact V _ _
      (@Scheme.compactSpace_of_isAffine V hVaff) hC.isRetrocompact

end AlgebraicGeometry
