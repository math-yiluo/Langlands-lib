import Langlands.Analysis.SeveralComplex.Hartogs.TaylorCoefficients
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

/-! # The Baire step of Hartogs' theorem

Let `B` be an open subset of a finite-dimensional complex normed space `E₁` and `D ⊆ ℂ` open.
A function `f : E₁ × ℂ → ℂ` that is holomorphic in each variable separately on `B × D` is jointly
holomorphic there (`differentiableOn_prod_complex_of_separately`).

Near a point `(z₀, w₀)`, the Baire category theorem in the `w`-variable gives a small ball
`ball w' ε` near `w₀` on which `f` is bounded uniformly in `z` (`exists_ball_forall_norm_le`).
Osgood's lemma makes `f` jointly holomorphic on `ball z₀ ρ × ball w' ε`. The extension step
`differentiableOn_prod_ball_of_small` then extends this to a product that contains
`(z₀, w₀)`. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open Metric Set Filter
open scoped Topology

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [FiniteDimensional ℂ E₁]

/-- **Baire step.** If `f (z, w)` is continuous in `z ∈ closedBall z₀ ρ` for each
`w ∈ ball w₀ t` and continuous in `w ∈ ball w₀ t` for each `z ∈ closedBall z₀ ρ`, then on some
ball `ball w' ε ⊆ ball w₀ t` the function `f` is bounded uniformly for
`z ∈ closedBall z₀ ρ`. -/
theorem exists_ball_forall_norm_le {f : E₁ × ℂ → ℂ} {z₀ : E₁} {ρ : ℝ} {w₀ : ℂ} {t : ℝ}
    (ht : 0 < t)
    (hcont₁ : ∀ w ∈ ball w₀ t, ContinuousOn (fun z => f (z, w)) (closedBall z₀ ρ))
    (hcont₂ : ∀ z ∈ closedBall z₀ ρ, ContinuousOn (fun w => f (z, w)) (ball w₀ t)) :
    ∃ w' ∈ ball w₀ t, ∃ ε > 0, ∃ N : ℝ, ball w' ε ⊆ ball w₀ t ∧
      ∀ z ∈ closedBall z₀ ρ, ∀ w ∈ ball w' ε, ‖f (z, w)‖ ≤ N := by
  have : ProperSpace E₁ := FiniteDimensional.proper ℂ E₁
  set Z : ℕ → Set ℂ :=
    fun N => {w | w ∈ ball w₀ t → ∀ z ∈ closedBall z₀ ρ, ‖f (z, w)‖ ≤ N} with hZ
  -- the sets `Z N` are closed
  have hZc : ∀ N, IsClosed (Z N) := by
    intro N
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro w hw
    simp only [hZ, mem_compl_iff, mem_ofPred_eq, not_imp, not_forall, not_le] at hw
    obtain ⟨hwb, z, hz, hlt⟩ := hw
    have h1 : ContinuousAt (fun w => ‖f (z, w)‖) w :=
      ((hcont₂ z hz).continuousAt (isOpen_ball.mem_nhds hwb)).norm
    have h2 : ∀ᶠ w' in 𝓝 w, (N : ℝ) < ‖f (z, w')‖ :=
      Filter.Tendsto.eventually h1 (lt_mem_nhds hlt)
    filter_upwards [h2, isOpen_ball.mem_nhds hwb] with w' hw' hw'b
    simp only [hZ, mem_compl_iff, mem_ofPred_eq, not_imp, not_forall, not_le]
    exact ⟨hw'b, z, hz, hw'⟩
  -- and they cover `ℂ`
  have hZu : ⋃ N, Z N = univ := by
    refine eq_univ_of_forall fun w => ?_
    by_cases hw : w ∈ ball w₀ t
    · obtain ⟨C, hC⟩ :=
        (isCompact_closedBall z₀ ρ).exists_bound_of_continuousOn (hcont₁ w hw)
      obtain ⟨N, hN⟩ := exists_nat_ge C
      exact mem_iUnion.2 ⟨N, fun _ z hz => (hC z hz).trans hN⟩
    · exact mem_iUnion.2 ⟨0, fun h => absurd h hw⟩
  -- Baire: some `interior (Z N)` meets `ball w₀ t`
  have hd := dense_iUnion_interior_of_closed hZc hZu
  obtain ⟨w', hw'U, hw'b⟩ := hd.exists_mem_open isOpen_ball ⟨w₀, mem_ball_self ht⟩
  obtain ⟨N, hN⟩ := mem_iUnion.1 hw'U
  have hnhds : interior (Z N) ∩ ball w₀ t ∈ 𝓝 w' :=
    inter_mem (isOpen_interior.mem_nhds hN) (isOpen_ball.mem_nhds hw'b)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 hnhds
  refine ⟨w', hw'b, ε, hε, N, fun w hw => (hεsub hw).2, fun z hz w hw => ?_⟩
  have hw2 := hεsub hw
  exact interior_subset hw2.1 hw2.2 z hz

/-- **Hartogs' theorem for `E₁ × ℂ`.** Let `E₁` be finite-dimensional and `B ⊆ E₁`, `D ⊆ ℂ`
open. If `f : E₁ × ℂ → ℂ` is holomorphic in `z ∈ B` for each `w ∈ D` and holomorphic in `w ∈ D`
for each `z ∈ B`, then `f` is holomorphic on `B × D`. -/
theorem differentiableOn_prod_complex_of_separately {B : Set E₁} {D : Set ℂ} (hB : IsOpen B)
    (hD : IsOpen D) {f : E₁ × ℂ → ℂ}
    (hf₁ : ∀ w ∈ D, DifferentiableOn ℂ (fun z => f (z, w)) B)
    (hf₂ : ∀ z ∈ B, DifferentiableOn ℂ (fun w => f (z, w)) D) :
    DifferentiableOn ℂ f (B ×ˢ D) := by
  rintro ⟨z₀, w₀⟩ ⟨hz₀, hw₀⟩
  obtain ⟨s, hs, hsB⟩ := Metric.isOpen_iff.1 hB z₀ hz₀
  obtain ⟨u, hu, huD⟩ := Metric.isOpen_iff.1 hD w₀ hw₀
  set ρ : ℝ := s / 2 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hcl : closedBall z₀ ρ ⊆ B := (closedBall_subset_ball (by linarith)).trans hsB
  have hBall : ball z₀ ρ ⊆ B := ball_subset_closedBall.trans hcl
  set t : ℝ := u / 3 with ht_def
  have ht : 0 < t := by positivity
  have htD : ball w₀ t ⊆ D := (ball_subset_ball (by linarith)).trans huD
  -- a ball `ball w' ε` near `w₀` on which `f` is bounded (Baire)
  obtain ⟨w', hw', ε, hε, N, hsub, hN⟩ := exists_ball_forall_norm_le ht
    (fun w hw => (hf₁ w (htD hw)).continuousOn.mono hcl)
    (fun z hz => (hf₂ z (hcl hz)).continuousOn.mono htD)
  -- joint holomorphy on `ball z₀ ρ × ball w' ε` (Osgood)
  have hsmall : DifferentiableOn ℂ f (ball z₀ ρ ×ˢ ball w' ε) := by
    refine differentiableOn_prod_of_locallyBounded isOpen_ball isOpen_ball
      (fun w hw => (hf₁ w (htD (hsub hw))).mono hBall)
      (fun z hz => (hf₂ z (hBall hz)).mono (hsub.trans htD)) ?_
    intro p hp
    refine ⟨N, ?_⟩
    filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds hp] with q hq
    exact hN q.1 (ball_subset_closedBall hq.1) q.2 hq.2
  -- extension to `ball z₀ ρ × ball w' (2t)`, which contains `(z₀, w₀)`
  have hbig : ball w' (2 * t) ⊆ D := by
    refine (ball_subset_ball' ?_).trans huD
    rw [mem_ball] at hw'
    linarith
  have hext := differentiableOn_prod_ball_of_small isOpen_ball hε
    (fun w hw => (hf₁ w (hbig hw)).mono hBall)
    (fun z hz => (hf₂ z (hBall hz)).mono hbig) hsmall
  have hmem : (z₀, w₀) ∈ ball z₀ ρ ×ˢ ball w' (2 * t) := by
    refine ⟨mem_ball_self hρ, ?_⟩
    rw [mem_ball, dist_comm]
    rw [mem_ball] at hw'
    linarith
  exact (hext.differentiableAt
    ((isOpen_ball.prod isOpen_ball).mem_nhds hmem)).differentiableWithinAt

end Langlands.Analysis.SeveralComplex
