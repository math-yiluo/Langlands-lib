import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Sequences

/-! # Completeness from discrete orbits and local cocompactness

An abstract form of the proof of KP Theorem 4.2.10: a metric space with an
isometric group action is complete when every orbit is discrete and every unit
ball lies in the orbit of one compact set.
-/

noncomputable section

open Filter Topology

namespace Langlands.Geometry.Metric.KP

variable {Γ X : Type*} [Group Γ] [MetricSpace X] [MulAction Γ X] [IsIsometricSMul Γ X]

/-- KP Theorem 4.2.10, abstract form. If each point `y` has a radius `ε` such that
every translate of `y` at distance `< ε` equals `y`, and each unit ball is
contained in the translates of a compact set, then `X` is complete.

The source takes a closed chamber for the compact set and uses Lemma 4.2.11
for the discreteness of orbits. -/
theorem completeSpace_of_discrete_orbits
    (hcover : ∀ x₀ : X, ∃ K : Set X, IsCompact K ∧
      ∀ x, dist x x₀ < 1 → ∃ g : Γ, ∃ k ∈ K, g • k = x)
    (hdisc : ∀ y : X, ∃ ε > 0, ∀ g : Γ, dist (g • y) y < ε → g • y = y) :
    CompleteSpace X := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hu 1 one_pos
  obtain ⟨K, hK, hKcover⟩ := hcover (u N)
  have hsel : ∀ j : ℕ, ∃ g : Γ, ∃ k ∈ K, g • k = u (j + N) :=
    fun j => hKcover _ (hN _ (Nat.le_add_left N j))
  choose g k hk hgk using hsel
  obtain ⟨y, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hk
  obtain ⟨ε, hε, hfix⟩ := hdisc y
  have hf : Tendsto (fun j => φ j + N) atTop atTop :=
    tendsto_atTop_mono (fun j => (hφ.id_le j).trans (Nat.le_add_right _ _)) tendsto_id
  have hv : CauchySeq fun j => u (φ j + N) := hu.comp_tendsto hf
  obtain ⟨M₁, hM₁⟩ := Metric.cauchySeq_iff.1 hv (ε / 3) (by positivity)
  obtain ⟨M₂, hM₂⟩ := Metric.tendsto_atTop.1 hlim (ε / 3) (by positivity)
  set M := max M₁ M₂
  have hconst : ∀ i ≥ M, g (φ i) • y = g (φ M) • y := by
    intro i hi
    have hlt : dist (g (φ i) • y) (g (φ M) • y) < ε := by
      calc dist (g (φ i) • y) (g (φ M) • y)
          ≤ dist (g (φ i) • y) (g (φ i) • k (φ i)) +
              dist (g (φ i) • k (φ i)) (g (φ M) • k (φ M)) +
              dist (g (φ M) • k (φ M)) (g (φ M) • y) := dist_triangle4 _ _ _ _
        _ = dist (k (φ i)) y + dist (u (φ i + N)) (u (φ M + N)) + dist (k (φ M)) y := by
          rw [dist_smul, dist_smul, dist_comm y, hgk, hgk]
        _ < ε / 3 + ε / 3 + ε / 3 := by
          gcongr
          · exact hM₂ i (le_of_max_le_right hi)
          · exact hM₁ i (le_of_max_le_left hi) M (le_max_left _ _)
          · exact hM₂ M (le_max_right _ _)
        _ = ε := by ring
    have hdist : dist (((g (φ M))⁻¹ * g (φ i)) • y) y = dist (g (φ i) • y) (g (φ M) • y) := by
      rw [← dist_smul (g (φ M)), smul_smul, mul_inv_cancel_left]
    have h := hfix ((g (φ M))⁻¹ * g (φ i)) (hdist ▸ hlt)
    have := congrArg (g (φ M) • ·) h
    simpa only [smul_smul, mul_inv_cancel_left] using this
  refine ⟨g (φ M) • y, tendsto_nhds_of_cauchySeq_of_subseq hu hf ?_⟩
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  have hlim' := tendsto_iff_dist_tendsto_zero.1 hlim
  refine hlim'.congr' ?_
  filter_upwards [eventually_ge_atTop M] with i hi
  change dist (k (φ i)) y = dist (u (φ i + N)) (g (φ M) • y)
  rw [← hconst i hi, ← hgk, dist_smul]

end Langlands.Geometry.Metric.KP
