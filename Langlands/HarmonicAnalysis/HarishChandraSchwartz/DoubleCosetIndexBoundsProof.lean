import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DoubleCosetIndexBoundsStatement

/-! # Algebraic calculus for finite double-coset indices -/

universe u v

namespace Langlands.HarishChandraSchwartz

private theorem relative_triangle {G : Type u} [Group G] (A B C : Subgroup G)
    (hAB : A.relIndex B ≠ 0) (hBC : B.relIndex C ≠ 0) :
    A.relIndex C ≠ 0 ∧ A.relIndex C ≤ A.relIndex B * B.relIndex C := by
  have hcut : A.relIndex (B ⊓ C) ≠ 0 := by
    intro h
    exact hAB (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  have hmeet : (A ⊓ B).relIndex C ≠ 0 := by
    rw [← Subgroup.relIndex_inf_mul_relIndex]
    exact mul_ne_zero hcut hBC
  refine ⟨Subgroup.relIndex_ne_zero_trans hAB hBC, ?_⟩
  calc A.relIndex C ≤ (A ⊓ B).relIndex C :=
        Subgroup.relIndex_le_of_le_left inf_le_left hmeet
    _ = A.relIndex (B ⊓ C) * B.relIndex C :=
      (Subgroup.relIndex_inf_mul_relIndex A B C).symm
    _ ≤ A.relIndex B * B.relIndex C :=
      Nat.mul_le_mul_right _ (Subgroup.relIndex_le_of_le_right inf_le_left hAB)

private theorem conjugate_comp {G : Type u} [Group G] (K : Subgroup G) (g h : G) :
    conjSubgroup (g * h) K = conjSubgroup g (conjSubgroup h K) := by
  ext x
  simp only [mem_conjSubgroup, mul_inv_rev, mul_assoc]

private theorem conjugate_index {G : Type u} [Group G]
    (A B : Subgroup G) (g : G) :
    (conjSubgroup g A).relIndex (conjSubgroup g B) = A.relIndex B := by
  unfold conjSubgroup
  rw [Subgroup.comap_equiv_eq_map_symm', Subgroup.comap_equiv_eq_map_symm']
  exact Subgroup.relIndex_map_map_of_injective A B (MulAut.conj g).injective

private theorem index_mul {G : Type u} [Group G] (K : Subgroup G) (g h : G)
    (hg : doubleCosetIndex K g ≠ 0) (hh : doubleCosetIndex K h ≠ 0) :
    doubleCosetIndex K (g * h) ≠ 0 ∧
      doubleCosetIndex K (g * h) ≤ doubleCosetIndex K g * doubleCosetIndex K h := by
  have heq : (conjSubgroup (g * h) K).relIndex (conjSubgroup g K) =
      doubleCosetIndex K h := by
    rw [conjugate_comp, conjugate_index]
    rfl
  have hb : (conjSubgroup (g * h) K).relIndex (conjSubgroup g K) ≠ 0 := by
    rwa [heq]
  obtain ⟨hfin, hle⟩ := relative_triangle (conjSubgroup (g * h) K)
    (conjSubgroup g K) K hb hg
  exact ⟨hfin, by simpa only [heq, doubleCosetIndex, mul_comm] using hle⟩

private theorem map_conjugate {G : Type u} {H : Type v} [Group G] [Group H]
    (f : G →* H) (K : Subgroup G) (g : G) :
    (conjSubgroup g K).map f = conjSubgroup (f g) (K.map f) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_conjSubgroup]
    exact ⟨g⁻¹ * x * g, mem_conjSubgroup.mp hx, by simp⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := mem_conjSubgroup.mp hy
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · exact mem_conjSubgroup.mpr (by simpa [mul_assoc] using hx)
    · simp [map_mul, map_inv, hxy, mul_assoc]

/-- The complete algebraic finite-index calculus statement. -/
theorem doubleCosetIndexBounds : DoubleCosetIndexBoundsStatement.{u,v} := by
  intro G _ K
  refine ⟨index_mul K, ?_, ?_⟩
  · intro g hg n
    induction n with
    | zero =>
      have hc : conjSubgroup (1 : G) K = K := by
        ext x
        simp [mem_conjSubgroup]
      have h1 : doubleCosetIndex K (1 : G) = 1 := by
        rw [doubleCosetIndex, hc, Subgroup.relIndex_self]
      simpa only [pow_zero, h1] using
        (show (1 : ℕ) ≠ 0 ∧ 1 ≤ 1 from ⟨one_ne_zero, le_rfl⟩)
    | succ n ih =>
      obtain ⟨hfin, hle⟩ := index_mul K (g ^ n) g ih.1 hg
      refine ⟨by simpa only [pow_succ] using hfin, ?_⟩
      simpa only [pow_succ] using hle.trans (Nat.mul_le_mul_right _ ih.2)
  · intro H _ f g hg
    unfold doubleCosetIndex at *
    rw [← map_conjugate, ← Subgroup.relIndex_comap, Subgroup.comap_map_eq]
    exact ⟨ne_zero_of_dvd_ne_zero hg
      (Subgroup.relIndex_dvd_of_le_left K le_sup_left),
      Subgroup.relIndex_le_of_le_left le_sup_left hg⟩

end Langlands.HarishChandraSchwartz
