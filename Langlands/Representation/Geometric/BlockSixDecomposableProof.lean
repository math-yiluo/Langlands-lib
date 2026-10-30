import Langlands.Representation.Geometric.BlockSixDecomposableStatement
import Langlands.Representation.Geometric.StandardIntersectionsProof
import Langlands.Representation.Geometric.GeneralIntersections

/-! Entrywise block projection and literal intersection decomposition. -/

namespace Langlands.Geometric

open GeneralLinear
open scoped Pointwise

universe uR

variable {n : ℕ} (R : Type uR) [CommRing R]

theorem embeddedLeviProjection_entry (B : BlockShape n)
    (g : B.parabolic R) (a b : Fin n) :
    B.leviEmbedding R (B.leviProjection R g) a b =
      if blockIndex B a = blockIndex B b then g.val a b else 0 := by
  classical
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective a
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective b
  change B.leviEmbedding R (B.leviProjection R g) (B.index i a) (B.index j b) =
    if blockIndex B (B.index i a) = blockIndex B (B.index j b) then
      g.val (B.index i a) (B.index j b) else 0
  simp only [blockIndex_index]
  split_ifs with hij
  · subst j
    simp only [B.leviEmbedding_apply_same, B.leviProjection_apply]
  · exact B.leviEmbedding_apply_ne R _ a b hij

theorem inversePermutation_conjugate_entry (w : Equiv.Perm (Fin n))
    (g : GeneralLinear n R) (a b : Fin n) :
    ((permutation n R w)⁻¹ * g * permutation n R w) a b =
      g (w a) (w b) := by
  simpa only [permutation_inv, inv_inv] using
    permutation_conjugate_entry n R w⁻¹ g a b

theorem conjugatedEmbeddedLeviProjection_entry (B : BlockShape n)
    (w : Equiv.Perm (Fin n)) (g : B.parabolic R) (a b : Fin n) :
    ((permutation n R w)⁻¹ *
      B.leviEmbedding R (B.leviProjection R g) * permutation n R w) a b =
      if blockIndex B (w a) = blockIndex B (w b) then
        ((permutation n R w)⁻¹ * g.val * permutation n R w) a b else 0 := by
  rw [inversePermutation_conjugate_entry,
    inversePermutation_conjugate_entry, embeddedLeviProjection_entry]

theorem embeddedLeviProjection_mem_conjugate_parabolic (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (g : B.parabolic R)
    (hg : g.val ∈ General.conjugate (C.parabolic R) (permutation n R w)) :
    B.leviEmbedding R (B.leviProjection R g) ∈
      General.conjugate (C.parabolic R) (permutation n R w) := by
  apply (General.mem_conjugate _ _ _).mpr
  apply (mem_parabolic_iff_blockIndex R C _).mpr
  have h := (mem_parabolic_iff_blockIndex R C _).mp
    ((General.mem_conjugate _ _ _).mp hg)
  intro a b hab
  rw [conjugatedEmbeddedLeviProjection_entry]
  split_ifs
  · exact h a b hab
  · rfl

theorem embeddedLeviProjection_mem_conjugate_levi (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (g : B.parabolic R)
    (hg : g.val ∈ General.conjugate (C.leviSubgroup R) (permutation n R w)) :
    B.leviEmbedding R (B.leviProjection R g) ∈
      General.conjugate (C.leviSubgroup R) (permutation n R w) := by
  apply (General.mem_conjugate _ _ _).mpr
  apply (CuspidalSupport.levi_mem_iff C _).mpr
  have h := (CuspidalSupport.levi_mem_iff C _).mp
    ((General.mem_conjugate _ _ _).mp hg)
  intro a b hab
  rw [conjugatedEmbeddedLeviProjection_entry]
  split_ifs
  · exact h a b hab
  · rfl

theorem embeddedLeviProjection_mem_conjugate_unipotent (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (g : B.parabolic R)
    (hg : g.val ∈ General.conjugate (C.unipotentSubgroup R) (permutation n R w)) :
    B.leviEmbedding R (B.leviProjection R g) ∈
      General.conjugate (C.unipotentSubgroup R) (permutation n R w) := by
  apply (General.mem_conjugate _ _ _).mpr
  apply (mem_unipotent_iff_blockIndex R C _).mpr
  have h := (mem_unipotent_iff_blockIndex R C _).mp
    ((General.mem_conjugate _ _ _).mp hg)
  refine ⟨?_, ?_⟩
  · apply (mem_parabolic_iff_blockIndex R C _).mpr
    have hp := (mem_parabolic_iff_blockIndex R C _).mp h.1
    intro a b hab
    rw [conjugatedEmbeddedLeviProjection_entry]
    split_ifs
    · exact hp a b hab
    · rfl
  · intro a b hab
    rw [conjugatedEmbeddedLeviProjection_entry]
    by_cases he : blockIndex B (w a) = blockIndex B (w b)
    · simp only [he, ↓reduceIte]
      exact h.2 a b hab
    · simp only [he, ↓reduceIte]
      have hne : a ≠ b := by
        intro heq
        subst b
        exact he rfl
      simp only [hne, ↓reduceIte]

theorem isDecomposable_of_embeddedLeviProjection_stable (B : BlockShape n)
    (H : Subgroup (GeneralLinear n R))
    (hH : ∀ g : B.parabolic R, g.val ∈ H →
      B.leviEmbedding R (B.leviProjection R g) ∈ H) :
    General.IsDecomposable H (B.leviSubgroup R) (B.unipotentSubgroup R) := by
  apply (General.isDecomposable_iff _ _ _).mpr
  intro g hg hmu
  have hp : g ∈ B.parabolic R := by
    rcases hmu with ⟨m, hm, u, hu, rfl⟩
    exact (B.parabolic R).mul_mem
      (B.leviAsParabolic R ⟨m, hm⟩).property
      ((B.mem_unipotentSubgroup_iff R u).mp hu).1
  let gp : B.parabolic R := ⟨g, hp⟩
  let m := B.leviEmbedding R (B.leviProjection R gp)
  let up : B.parabolic R :=
    (B.leviInParabolic R (B.leviProjection R gp))⁻¹ * gp
  have hmH : m ∈ H := hH gp hg
  have hup : up ∈ B.unipotentRadical R := by
    change B.leviProjection R up = 1
    simp only [up, map_mul, map_inv, B.leviProjection_section, inv_mul_cancel]
  have huH : (up : GeneralLinear n R) ∈ H := by
    change m⁻¹ * g ∈ H
    exact H.mul_mem (H.inv_mem hmH) hg
  refine ⟨m, ⟨hmH, ⟨B.leviProjection R gp, rfl⟩⟩,
    (up : GeneralLinear n R), ⟨huH, ⟨up, hup, rfl⟩⟩, ?_⟩
  change m * (m⁻¹ * g) = g
  exact mul_inv_cancel_left m g

theorem conjugate_blockParabolic_isDecomposable (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) :
    General.IsDecomposable (General.conjugate (C.parabolic R) (permutation n R w))
      (B.leviSubgroup R) (B.unipotentSubgroup R) :=
  isDecomposable_of_embeddedLeviProjection_stable R B _
    (embeddedLeviProjection_mem_conjugate_parabolic R B C w)

theorem conjugate_blockLevi_isDecomposable (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) :
    General.IsDecomposable (General.conjugate (C.leviSubgroup R) (permutation n R w))
      (B.leviSubgroup R) (B.unipotentSubgroup R) :=
  isDecomposable_of_embeddedLeviProjection_stable R B _
    (embeddedLeviProjection_mem_conjugate_levi R B C w)

theorem conjugate_blockUnipotent_isDecomposable (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) :
    General.IsDecomposable
      (General.conjugate (C.unipotentSubgroup R) (permutation n R w))
      (B.leviSubgroup R) (B.unipotentSubgroup R) :=
  isDecomposable_of_embeddedLeviProjection_stable R B _
    (embeddedLeviProjection_mem_conjugate_unipotent R B C w)

theorem blockParabolic_sixDecomposable (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) :
    General.SixDecomposable
      (B.parabolic R) (B.leviSubgroup R) (B.unipotentSubgroup R)
      (C.parabolic R) (C.leviSubgroup R) (C.unipotentSubgroup R)
      (permutation n R w) := by
  refine ⟨conjugate_blockParabolic_isDecomposable R C B w,
    conjugate_blockLevi_isDecomposable R C B w,
    conjugate_blockUnipotent_isDecomposable R C B w, ?_, ?_, ?_⟩
  · simpa only [permutation_inv] using
      conjugate_blockParabolic_isDecomposable R B C w⁻¹
  · simpa only [permutation_inv] using
      conjugate_blockLevi_isDecomposable R B C w⁻¹
  · simpa only [permutation_inv] using
      conjugate_blockUnipotent_isDecomposable R B C w⁻¹

/-- The unapplied exact statement, with its arbitrary ring universe retained. -/
theorem blockParabolicSixDecomposable : BlockParabolicSixDecomposable.{uR} := by
  intro R _ n B C w
  exact blockParabolic_sixDecomposable R B C w

end Langlands.Geometric
