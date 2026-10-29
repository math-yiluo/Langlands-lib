import Langlands.Group.GL.UpperBruhatLocalClosednessStatement
import Langlands.Group.GL.UpperBruhatRankProof
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.LocallyClosed

/-! Local closedness of the actual upper Bruhat cells via their corner-rank profiles. -/

namespace Langlands.GeneralLinear

universe u

section RankTopology

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] {n : ℕ}

private theorem isOpen_matrix_rank_ge (k : ℕ) :
    IsOpen {A : Matrix (Fin n) (Fin n) K | k ≤ A.rank} := by
  classical
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro A hA
  obtain ⟨V, U, e, _, _, hnormal⟩ := Matrix.exists_rank_normal_form A
  let f : Fin k → Fin n := fun a => e.symm (Sum.inl (Fin.castLE hA a))
  have hminor : (V * A * U).submatrix f f = (1 : Matrix (Fin k) (Fin k) K) := by
    ext a b
    rw [hnormal]
    simp only [Matrix.submatrix_apply, f, Equiv.apply_symm_apply,
      Matrix.fromBlocks_apply₁₁]
    simp [Matrix.one_apply, Fin.ext_iff]
  refine ⟨{B : Matrix (Fin n) (Fin n) K | ((V * B * U).submatrix f f).det ≠ 0},
    ?_, ?_, ?_⟩
  · intro B hB
    change k ≤ B.rank
    have hr := Matrix.rank_of_det_ne_zero hB
    have hs := Matrix.rank_submatrix_le (V * B * U) f f
    have hm : (V * B * U).rank ≤ B.rank :=
      (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    simpa only [hr, Fintype.card_fin] using hs.trans hm
  · exact isOpen_ne_fun
      (((continuous_const.mul continuous_id).mul continuous_const).matrix_submatrix f f).matrix_det
      continuous_const
  · simp only [Set.mem_ofPred_eq, hminor, Matrix.det_one, ne_eq, one_ne_zero, not_false_eq_true]

private theorem isClosed_matrix_rank_le (k : ℕ) :
    IsClosed {A : Matrix (Fin n) (Fin n) K | A.rank ≤ k} := by
  have hopen := isOpen_matrix_rank_ge (K := K) (n := n) (k + 1)
  convert hopen.isClosed_compl using 1
  ext A
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
  omega

private theorem isLocallyClosed_matrix_rank_eq (k : ℕ) :
    IsLocallyClosed {A : Matrix (Fin n) (Fin n) K | A.rank = k} := by
  refine ⟨{A | k ≤ A.rank}, {A | A.rank ≤ k},
    isOpen_matrix_rank_ge k, isClosed_matrix_rank_le k, ?_⟩
  ext A
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  exact ⟨fun h => ⟨h.ge, h.le⟩, fun h => le_antisymm h.2 h.1⟩

private theorem isLocallyClosed_matrix_rank_profile
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (f : I → X → Matrix (Fin n) (Fin n) K) (hf : ∀ i, Continuous (f i))
    (k : I → ℕ) :
    IsLocallyClosed {x : X | ∀ i, (f i x).rank = k i} := by
  refine ⟨⋂ i, (f i) ⁻¹' {A | k i ≤ A.rank},
    ⋂ i, (f i) ⁻¹' {A | A.rank ≤ k i}, ?_, ?_, ?_⟩
  · exact isOpen_iInter_of_finite fun i => (isOpen_matrix_rank_ge (k i)).preimage (hf i)
  · exact isClosed_iInter fun i => (isClosed_matrix_rank_le (k i)).preimage (hf i)
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
    exact ⟨fun h => ⟨fun i => (h i).ge, fun i => (h i).le⟩,
      fun h i => le_antisymm (h.2 i) (h.1 i)⟩

omit [IsTopologicalRing K] [T2Space K] in
private theorem continuous_lowerLeftCorner (i j : Fin (n + 1)) :
    Continuous (fun g : Langlands.GeneralLinear n K =>
      ((fun r c : Fin n =>
        if i.val ≤ r.val ∧ c.val < j.val then g r c else 0) :
        Matrix (Fin n) (Fin n) K)) := by
  have hv : Continuous (fun g : Langlands.GeneralLinear n K =>
      (g.val : Matrix (Fin n) (Fin n) K)) := Units.continuous_val
  apply continuous_pi
  intro r
  apply continuous_pi
  intro c
  by_cases h : i.val ≤ r.val ∧ c.val < j.val
  · simp only [ite_eq_left h]
    exact (continuous_apply c).comp ((continuous_apply r).comp hv)
  · simp only [ite_eq_right h]
    exact continuous_const

private theorem upperBruhatCell_isLocallyClosed_of_rank_characterization
    (w : Equiv.Perm (Fin n))
    (hrank : ∀ g : Langlands.GeneralLinear n K,
      g ∈ upperBruhatCell n K w ↔ ∀ i j : Fin (n + 1),
        Matrix.rank (fun r c : Fin n =>
          if i.val ≤ r.val ∧ c.val < j.val then g r c else (0 : K)) =
        Matrix.rank (fun r c : Fin n =>
          if i.val ≤ r.val ∧ c.val < j.val then permutation n K w r c else (0 : K))) :
    IsLocallyClosed (upperBruhatCell n K w) := by
  classical
  let f : (Fin (n + 1) × Fin (n + 1)) →
      Langlands.GeneralLinear n K → Matrix (Fin n) (Fin n) K :=
    fun ij g r c =>
      if ij.1.val ≤ r.val ∧ c.val < ij.2.val then g r c else 0
  let k : (Fin (n + 1) × Fin (n + 1)) → ℕ :=
    fun ij => Matrix.rank (fun r c : Fin n =>
      if ij.1.val ≤ r.val ∧ c.val < ij.2.val then permutation n K w r c else (0 : K))
  have hprofile := isLocallyClosed_matrix_rank_profile f
    (fun ij => continuous_lowerLeftCorner ij.1 ij.2) k
  convert hprofile using 1
  ext g
  simpa only [Set.mem_ofPred_eq, Prod.forall] using hrank g

end RankTopology

private theorem upperBruhatLocalClosedness_of_rank_characterization
    (hrank : UpperBruhatRankCharacterizationStatement.{u}) :
    UpperBruhatLocalClosednessStatement.{u} := by
  intro K _ _ _ _ n w
  exact upperBruhatCell_isLocallyClosed_of_rank_characterization w (hrank K n w)

/-- Every actual upper Bruhat cell is locally closed over every Hausdorff topological field. -/
theorem upperBruhatLocalClosedness : UpperBruhatLocalClosednessStatement.{u} :=
  upperBruhatLocalClosedness_of_rank_characterization upperBruhatRankCharacterization

end Langlands.GeneralLinear
