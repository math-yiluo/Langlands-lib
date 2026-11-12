import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-! # The maximal positive-part argument in Langlands exhaustion

The norm argument of Renard VII.4.2(iii) follows from the nonpositive
inner-product characterization of a cone projection. The actual exponent
family, its finiteness, and its identification with these vectors are not
constructed here.
-/

noncomputable section

universe u v

namespace Langlands.Renard

variable {ι : Type u} {E : Type v} [NormedAddCommGroup E]

/-- Choose a member of a nonempty finite family with maximal positive-part
norm. The construction retains the member's original index. -/
def maximalPositiveProjectionIndex (s : Finset ι) (hs : s.Nonempty)
    (positive : ι → E) : {j // j ∈ s} :=
  ⟨(s.exists_max_image (fun j => ‖positive j‖) hs).choose,
    (s.exists_max_image (fun j => ‖positive j‖) hs).choose_spec.1⟩

theorem norm_le_maximalPositiveProjectionIndex (s : Finset ι) (hs : s.Nonempty)
    (positive : ι → E) {j : ι} (hj : j ∈ s) :
    ‖positive j‖ ≤ ‖positive (maximalPositiveProjectionIndex s hs positive).val‖ :=
  (s.exists_max_image (fun j => ‖positive j‖) hs).choose_spec.2 j hj

variable [InnerProductSpace ℝ E]

/-- Orthogonality to a point of `C`, a polar residual, and the maximal-norm
bound force the new positive part to equal that point. -/
theorem positivePart_eq_of_norm_le {C : Set E} {μ ξ p : E}
    (hμ : μ ∈ C) (horth : inner ℝ ξ μ = 0)
    (hres : ∀ c ∈ C, inner ℝ (ξ + μ - p) c ≤ 0)
    (hnorm : ‖p‖ ≤ ‖μ‖) : p = μ := by
  have hinner := hres μ hμ
  rw [inner_sub_left, inner_add_left, horth, real_inner_self_eq_norm_sq] at hinner
  have hsq : ‖p‖ ^ 2 ≤ ‖μ‖ ^ 2 := by
    nlinarith [norm_nonneg p, norm_nonneg μ]
  have hzero : ‖p - μ‖ = 0 := by
    have hdiff := norm_sub_sq_real p μ
    nlinarith [sq_nonneg ‖p - μ‖, norm_nonneg (p - μ)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- In the same situation the original orthogonal perturbation is itself in
the negative polar: its inner product with every point of `C` is nonpositive. -/
theorem nonpositive_inner_of_maximal_positivePart {C : Set E} {μ ξ p : E}
    (hμ : μ ∈ C) (horth : inner ℝ ξ μ = 0)
    (hres : ∀ c ∈ C, inner ℝ (ξ + μ - p) c ≤ 0)
    (hnorm : ‖p‖ ≤ ‖μ‖) :
    p = μ ∧ ∀ c ∈ C, inner ℝ ξ c ≤ 0 := by
  have hp := positivePart_eq_of_norm_le hμ horth hres hnorm
  refine ⟨hp, ?_⟩
  simpa only [hp, add_sub_cancel_right] using hres

/-- For a finite family, selecting the maximal positive part supplies the norm
bound. Every orthogonal difference that occurs in the family is negative
polar whenever that member has a negative-polar residual. -/
theorem nonpositive_inner_of_maximalPositiveProjectionIndex
    (s : Finset ι) (hs : s.Nonempty) (parameter positive : ι → E)
    {C : Set E} {j : ι} (hj : j ∈ s)
    (hμ : positive (maximalPositiveProjectionIndex s hs positive).val ∈ C)
    (horth : inner ℝ
      (parameter j - positive (maximalPositiveProjectionIndex s hs positive).val)
      (positive (maximalPositiveProjectionIndex s hs positive).val) = 0)
    (hres : ∀ c ∈ C, inner ℝ (parameter j - positive j) c ≤ 0) :
    positive j = positive (maximalPositiveProjectionIndex s hs positive).val ∧
      ∀ c ∈ C, inner ℝ
        (parameter j - positive (maximalPositiveProjectionIndex s hs positive).val) c ≤ 0 := by
  apply nonpositive_inner_of_maximal_positivePart hμ horth
  · simpa only [sub_add_cancel] using hres
  · exact norm_le_maximalPositiveProjectionIndex s hs positive hj

end Langlands.Renard
