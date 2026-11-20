import Langlands.LinearAlgebra.MatrixSpectralClustering
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Rank strata with varying matrix spectrum -/

noncomputable section

open Filter Matrix
open scoped Topology

set_option autoImplicit false

namespace Langlands

/-- Matrix rank cannot decrease under a sufficiently small perturbation over a complete
nontrivially normed field. -/
theorem isOpen_matrixRank_ge {K I J : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    [Fintype I] [Fintype J] (r : ℕ) :
    IsOpen {A : Matrix I J K | r ≤ A.rank} := by
  let L (A : Matrix I J K) : (J → K) →L[K] (I → K) := A.mulVecLin.toContinuousLinearMap
  have hL : Continuous L := continuous_clm_apply.mpr (fun x =>
    continuous_id.matrix_mulVec (continuous_const (y := x)))
  have hRank (A : Matrix I J K) : (A.rank : Cardinal) = (L A).toLinearMap.rank :=
    Module.finrank_eq_rank K _
  convert (isOpen_setOfPred_nat_le_rank r).preimage hL using 1
  ext A
  change r ≤ A.rank ↔ (r : Cardinal) ≤ (L A).toLinearMap.rank
  rw [← hRank]
  exact_mod_cast (Iff.rfl : r ≤ A.rank ↔ r ≤ A.rank)

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

/-- Rank of the `k`th power of a matrix minus a scalar matrix. -/
def shiftedMatrixRank (A : Mat) (z : ℂ) (k : ℕ) : ℕ :=
  ((A - z • (1 : Mat)) ^ k).rank

private theorem exists_radius_of_eventually_prod {X : Type*} [TopologicalSpace X]
    {a : X} {z : ℂ} {p : X → ℂ → Prop}
    (h : ∀ᶠ q in 𝓝 (a, z), p q.1 q.2) :
    ∃ ε > 0, ∀ᶠ b in 𝓝 a, ∀ w : ℂ, dist w z < ε → p b w := by
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp h
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨r, hr, ?_⟩
  filter_upwards [hU] with b hb w hw
  have hwV : w ∈ V := hrV (Metric.mem_ball.mpr hw)
  have hBw : (b, w) ∈ U ×ˢ V := ⟨hb, hwV⟩
  exact hUV hBw

private theorem eventually_shiftedMatrixRank_ge (A : Mat) (z : ℂ) (k : ℕ) :
    ∃ ε > 0, ∀ᶠ B in 𝓝 A, ∀ w : ℂ, dist w z < ε →
      shiftedMatrixRank A z k ≤ shiftedMatrixRank B w k := by
  let g (p : Mat × ℂ) : Mat := (p.1 - p.2 • (1 : Mat)) ^ k
  have hg : Continuous g := (continuous_fst.sub (continuous_snd.smul continuous_const)).pow k
  let R : Set Mat := {B | (g (A, z)).rank ≤ B.rank}
  have hR : IsOpen R := isOpen_matrixRank_ge _
  have hbase : g (A, z) ∈ R := Set.mem_ofPred.mpr le_rfl
  have h := hg.continuousAt.eventually (hR.mem_nhds hbase)
  exact exists_radius_of_eventually_prod
    (p := fun B w => shiftedMatrixRank A z k ≤ shiftedMatrixRank B w k) h

/-- Near a matrix, the matching of distinct roots on the fixed-count locus can be chosen
so that ranks of all shifted powers through the matrix dimension only increase. -/
theorem eventually_matrixSpectralRanks_mono (A : Mat) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B in 𝓝 A, (matrixSpectralRoots A).card ≤ (matrixSpectralRoots B).card ∧
      ((matrixSpectralRoots B).card = (matrixSpectralRoots A).card →
        ∃ e : matrixSpectralRoots A ≃ matrixSpectralRoots B,
          ∀ z : matrixSpectralRoots A, dist (e z : ℂ) (z : ℂ) < ε ∧
            B.charpoly.roots.count (e z : ℂ) = A.charpoly.roots.count (z : ℂ) ∧
            ∀ k : Fin (n + 1), shiftedMatrixRank A z k ≤ shiftedMatrixRank B (e z) k) := by
  classical
  let I := (matrixSpectralRoots A) × Fin (n + 1)
  have H (i : I) := eventually_shiftedMatrixRank_ge A i.1 i.2
  choose r hr hnear using H
  let s := insert ε (Finset.univ.image r)
  have hsn : s.Nonempty := Finset.insert_nonempty _ _
  let δ := s.inf' hsn id
  have hδ : 0 < δ := by
    apply (Finset.lt_inf'_iff hsn).mpr
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hε
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
      exact hr i
  have hδε : δ ≤ ε := Finset.inf'_le _ (Finset.mem_insert_self _ _)
  have hδr (i : I) : δ ≤ r i :=
    Finset.inf'_le _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem r (Finset.mem_univ i)))
  filter_upwards [eventually_matrixSpectralRoots_equiv A hδ, Filter.eventually_all.mpr hnear]
    with B hB hR
  refine ⟨hB.1, fun hd => ?_⟩
  obtain ⟨e, he⟩ := hB.2 hd
  exact ⟨e, fun z => ⟨(he z).1.trans_le hδε, (he z).2,
    fun k => hR (z, k) (e z) ((he z).1.trans_le (hδr (z, k)))⟩⟩

/-- Sum of shifted power ranks over the distinct characteristic roots and powers through `n`. -/
def matrixSpectralRankSum (A : Mat) : ℕ :=
  ∑ z ∈ matrixSpectralRoots A, ∑ k : Fin (n + 1), shiftedMatrixRank A z k

/-- A lexicographic label given by the distinct root count and the total shifted power rank. -/
def matrixSpectralRankLabel (A : Mat) : ℕ ×ₗ ℕ :=
  toLex ((matrixSpectralRoots A).card, matrixSpectralRankSum A)

private theorem spectralRankSum_eq_sum (A : Mat) :
    matrixSpectralRankSum A = ∑ z : matrixSpectralRoots A, ∑ k : Fin (n + 1),
      shiftedMatrixRank A z k :=
  (Finset.sum_coe_sort (matrixSpectralRoots A) (fun z =>
    ∑ k : Fin (n + 1), shiftedMatrixRank A z k)).symm

private theorem spectralRankSum_reindex {A B : Mat} (e : matrixSpectralRoots A ≃ matrixSpectralRoots B) :
    matrixSpectralRankSum B = ∑ z : matrixSpectralRoots A, ∑ k : Fin (n + 1),
      shiftedMatrixRank B (e z) k := by
  rw [spectralRankSum_eq_sum B,
    e.sum_comp (fun z : matrixSpectralRoots B => ∑ k : Fin (n + 1), shiftedMatrixRank B z k)]

/-- The lexicographic spectral rank label cannot decrease near a fixed matrix. -/
theorem eventually_matrixSpectralRankLabel_ge (A : Mat) :
    ∀ᶠ B in 𝓝 A, matrixSpectralRankLabel A ≤ matrixSpectralRankLabel B := by
  filter_upwards [eventually_matrixSpectralRanks_mono A zero_lt_one] with B hB
  apply Prod.Lex.toLex_le_toLex.mpr
  rcases lt_or_eq_of_le hB.1 with hlt | heq
  · exact Or.inl hlt
  · obtain ⟨e, he⟩ := hB.2 heq.symm
    refine Or.inr ⟨heq, ?_⟩
    change matrixSpectralRankSum A ≤ matrixSpectralRankSum B
    rw [spectralRankSum_reindex e, spectralRankSum_eq_sum A]
    exact Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun k _ => (he z).2.2 k

/-- On the fixed-label locus, local root matching preserves all the individual shifted
power ranks, since none decreases and their total stays constant. -/
theorem eventually_matrixSpectralRanks_eq_of_label_eq (A : Mat) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B in 𝓝 A, matrixSpectralRankLabel B = matrixSpectralRankLabel A →
      ∃ e : matrixSpectralRoots A ≃ matrixSpectralRoots B,
        ∀ z : matrixSpectralRoots A, dist (e z : ℂ) (z : ℂ) < ε ∧
          B.charpoly.roots.count (e z : ℂ) = A.charpoly.roots.count (z : ℂ) ∧
          ∀ k : Fin (n + 1), shiftedMatrixRank B (e z) k = shiftedMatrixRank A z k := by
  filter_upwards [eventually_matrixSpectralRanks_mono A hε] with B hB heq
  have hd := congrArg (fun q : ℕ ×ₗ ℕ => (ofLex q).1) heq
  have hs := congrArg (fun q : ℕ ×ₗ ℕ => (ofLex q).2) heq
  change matrixSpectralRankSum B = matrixSpectralRankSum A at hs
  obtain ⟨e, he⟩ := hB.2 hd
  rw [spectralRankSum_reindex e, spectralRankSum_eq_sum A] at hs
  have hsum : ∀ z : matrixSpectralRoots A, (∑ k : Fin (n + 1), shiftedMatrixRank A z k) =
      ∑ k : Fin (n + 1), shiftedMatrixRank B (e z) k := fun z =>
    (Finset.sum_eq_sum_iff_of_le (fun z _ => Finset.sum_le_sum fun k _ => (he z).2.2 k)).mp
      hs.symm z (Finset.mem_univ z)
  refine ⟨e, fun z => ⟨(he z).1, (he z).2.1, fun k => ?_⟩⟩
  exact ((Finset.sum_eq_sum_iff_of_le (fun k _ => (he z).2.2 k)).mp
    (hsum z) k (Finset.mem_univ k)).symm

theorem isOpen_matrixSpectralRankLabel_gt (p : ℕ ×ₗ ℕ) :
    IsOpen {A : Mat | p < matrixSpectralRankLabel A} :=
  isOpen_iff_mem_nhds.mpr fun A hA =>
    (eventually_matrixSpectralRankLabel_ge A).mono fun _ h => lt_of_lt_of_le hA h

theorem card_matrixSpectralRoots_le (A : Mat) : (matrixSpectralRoots A).card ≤ n := by
  refine (Multiset.toFinset_card_le A.charpoly.roots).trans ?_
  rw [← (IsAlgClosed.splits A.charpoly).natDegree_eq_card_roots]
  simp

theorem matrixSpectralRankSum_le (A : Mat) : matrixSpectralRankSum A ≤ n * ((n + 1) * n) := by
  calc
    matrixSpectralRankSum A ≤ ∑ z ∈ matrixSpectralRoots A, ∑ _ : Fin (n + 1), n :=
      Finset.sum_le_sum fun z _ => Finset.sum_le_sum fun k _ =>
        rank_le_width ((A - z • 1) ^ (k : ℕ))
    _ = (matrixSpectralRoots A).card * ((n + 1) * n) := by simp
    _ ≤ n * ((n + 1) * n) := Nat.mul_le_mul_right _ (card_matrixSpectralRoots_le A)

theorem shiftedMatrixRank_transpose (A : Mat) (z : ℂ) (k : ℕ) :
    shiftedMatrixRank Aᵀ z k = shiftedMatrixRank A z k := by
  have h : Aᵀ - z • (1 : Mat) = (A - z • (1 : Mat))ᵀ := by simp
  simp only [shiftedMatrixRank, h, ← transpose_pow, rank_transpose]

theorem shiftedMatrixRank_units_conj (u : Matˣ) (A : Mat) (z : ℂ) (k : ℕ) :
    shiftedMatrixRank ((u : Mat) * A * (↑u⁻¹ : Mat)) z k = shiftedMatrixRank A z k := by
  let B : Mat := (u : Mat) * A * (↑u⁻¹ : Mat)
  have h : (u : Mat) * A = B * (u : Mat) := by simp [B, mul_assoc]
  have hs : SemiconjBy (u : Mat) (A - z • (1 : Mat)) (B - z • (1 : Mat)) := by
    show (u : Mat) * (A - z • (1 : Mat)) = (B - z • (1 : Mat)) * (u : Mat)
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul, h]
  have he := (hs.pow_right k).eq
  change ((B - z • (1 : Mat)) ^ k).rank = ((A - z • (1 : Mat)) ^ k).rank
  rw [← rank_mul_eq_left_of_isUnit_det (u : Mat) _ (isUnits_det_units u), ← he,
    rank_mul_eq_right_of_isUnit_det _ _ (isUnits_det_units u)]

theorem matrixSpectralRankLabel_transpose (A : Mat) :
    matrixSpectralRankLabel Aᵀ = matrixSpectralRankLabel A := by
  simp only [matrixSpectralRankLabel, matrixSpectralRankSum, matrixSpectralRoots,
    charpoly_transpose, shiftedMatrixRank_transpose]

theorem matrixSpectralRankLabel_units_conj (u : Matˣ) (A : Mat) :
    matrixSpectralRankLabel ((u : Mat) * A * (↑u⁻¹ : Mat)) = matrixSpectralRankLabel A := by
  have h : ((u : Mat) * A * (↑u⁻¹ : Mat)).charpoly = A.charpoly := by
    simpa only [coe_units_inv] using charpoly_units_conj u A
  simp only [matrixSpectralRankLabel, matrixSpectralRankSum, matrixSpectralRoots,
    h, shiftedMatrixRank_units_conj]

end Langlands
