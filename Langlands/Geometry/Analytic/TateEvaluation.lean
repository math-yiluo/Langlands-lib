import Langlands.Geometry.Analytic.TateEvaluation.Definitions
import Langlands.Geometry.Analytic.Affinoid

/-! # Bounded evaluation of strictly convergent power series -/

noncomputable section

universe u v w

namespace Langlands.Analytic.StrictTateAlgebra

open Filter
open scoped Topology

variable (σ : Type u) (K : Type v) (B : Type w)
  [NormedField K] [IsUltrametricDist K]
  [NormedCommRing B] [NormedAlgebra K B]

theorem monomialValue_add (b : σ → B) (d e : σ →₀ ℕ) :
    monomialValue σ B b (d + e) = monomialValue σ B b d * monomialValue σ B b e :=
  Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem monomialValue_norm_le [NormOneClass B] (b : σ → B)
    (hb : ∀ i, ‖b i‖ ≤ 1) (d : σ →₀ ℕ) :
    ‖monomialValue σ B b d‖ ≤ 1 := by
  classical
  unfold monomialValue Finsupp.prod
  apply (Finset.norm_prod_le _ _).trans
  apply Finset.prod_le_one₀
  · intro i _
    exact norm_nonneg _
  · intro i _
    exact (norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) (hb i))

theorem hasBoundedMonomials_of_norm_le [NormOneClass B] (b : σ → B)
    (hb : ∀ i, ‖b i‖ ≤ 1) : HasBoundedMonomials σ B b :=
  ⟨1, zero_lt_one, monomialValue_norm_le σ B b hb⟩

theorem HasBoundedMonomials.pow_bound {b : σ → B}
    (hb : HasBoundedMonomials σ B b) (i : σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖b i ^ n‖ ≤ C := by
  classical
  obtain ⟨C, hCpos, hC⟩ := hb
  refine ⟨C, hCpos, fun n => ?_⟩
  simpa [monomialValue] using hC (Finsupp.single i n)

/-- For finitely many arguments, individual power bounds give one bound for
all monomials. The empty tuple and unnormalized target unit are included. -/
theorem hasBoundedMonomials_iff_pow_bound [Fintype σ] (b : σ → B) :
    HasBoundedMonomials σ B b ↔
      ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖b i ^ n‖ ≤ C := by
  classical
  constructor
  · exact fun h i => h.pow_bound σ B i
  · intro h
    choose C hCpos hC using h
    refine ⟨max 1 (max ‖(1 : B)‖ (∏ i, C i)),
      lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun d => ?_⟩
    unfold monomialValue
    rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rcases (Finset.univ : Finset σ).eq_empty_or_nonempty with hempty | hnonempty
    · rw [hempty, Finset.prod_empty]
      exact (le_max_left _ _).trans (le_max_right _ _)
    · exact ((Finset.norm_prod_le' _ hnonempty _).trans
        (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hC i (d i)))).trans
        ((le_max_right _ _).trans (le_max_right _ _))

theorem evaluationTerm_norm_le [NormOneClass B] (b : σ → B) (hb : ∀ i, ‖b i‖ ≤ 1)
    (f : StrictTateAlgebra σ K) (d : σ →₀ ℕ) :
    ‖evaluationTerm σ K B b f d‖ ≤ ‖MvPowerSeries.coeff d (series σ K f)‖ := by
  unfold evaluationTerm
  apply (norm_mul_le _ _).trans
  rw [norm_algebraMap']
  exact mul_le_of_le_one_right (norm_nonneg _) (monomialValue_norm_le σ B b hb d)

theorem evaluationTerm_norm_le_bound (b : σ → B) (C : ℝ)
    (hC : ∀ d : σ →₀ ℕ, ‖monomialValue σ B b d‖ ≤ C)
    (f : StrictTateAlgebra σ K) (d : σ →₀ ℕ) :
    ‖evaluationTerm σ K B b f d‖ ≤
      (max 1 ‖(1 : B)‖ * C) * ‖MvPowerSeries.coeff d (series σ K f)‖ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  unfold evaluationTerm
  calc
    ‖algebraMap K B (MvPowerSeries.coeff d (series σ K f)) * monomialValue σ B b d‖
        ≤ ‖algebraMap K B (MvPowerSeries.coeff d (series σ K f))‖ * C :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (hC d) (norm_nonneg _))
    _ = (‖MvPowerSeries.coeff d (series σ K f)‖ * ‖(1 : B)‖) * C := by
      rw [_root_.norm_algebraMap]
    _ ≤ (‖MvPowerSeries.coeff d (series σ K f)‖ * max 1 ‖(1 : B)‖) * C :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)) hC0
    _ = _ := by ring

variable [IsUltrametricDist B] [CompleteSpace B]

theorem summable_evaluationTerms (b : σ → B) (hb : HasBoundedMonomials σ B b)
    (f : StrictTateAlgebra σ K) : Summable (evaluationTerm σ K B b f) := by
  obtain ⟨C, _, hC⟩ := hb
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := zero_at_infty (coefficients σ K f)
  rw [Filter.cocompact_eq_cofinite] at h
  change Tendsto (fun d : σ →₀ ℕ => MvPowerSeries.coeff d (series σ K f))
    cofinite (𝓝 0) at h
  apply squeeze_zero (fun _ => norm_nonneg _)
    (evaluationTerm_norm_le_bound σ K B b C hC f)
  simpa only [mul_zero] using
    tendsto_const_nhds.mul (tendsto_zero_iff_norm_tendsto_zero.mp h)

omit [CompleteSpace B] in
theorem evaluate_norm_le [NormOneClass B] (b : σ → B) (hb : ∀ i, ‖b i‖ ≤ 1)
    (f : StrictTateAlgebra σ K) : ‖evaluate σ K B b f‖ ≤ ‖f‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _)
    (fun d => (evaluationTerm_norm_le σ K B b hb f d).trans (norm_coeff_le σ K f d))

omit [CompleteSpace B] in
theorem evaluate_norm_le_bound (b : σ → B) (C : ℝ)
    (hC : ∀ d : σ →₀ ℕ, ‖monomialValue σ B b d‖ ≤ C)
    (f : StrictTateAlgebra σ K) :
    ‖evaluate σ K B b f‖ ≤ (max 1 ‖(1 : B)‖ * C) * ‖f‖ := by
  have hD : 0 ≤ max 1 ‖(1 : B)‖ * C :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _))
      ((norm_nonneg _).trans (hC 0))
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg hD (norm_nonneg _)) (fun d =>
      (evaluationTerm_norm_le_bound σ K B b C hC f d).trans
        (mul_le_mul_of_nonneg_left (norm_coeff_le σ K f d) hD))

theorem evaluate_add (b : σ → B) (hb : HasBoundedMonomials σ B b)
    (f g : StrictTateAlgebra σ K) :
    evaluate σ K B b (f + g) = evaluate σ K B b f + evaluate σ K B b g := by
  have ht : evaluationTerm σ K B b (f + g) =
      fun d => evaluationTerm σ K B b f d + evaluationTerm σ K B b g d := by
    funext d
    change algebraMap K B (MvPowerSeries.coeff d (f.val + g.val)) * _ = _
    rw [map_add, map_add, add_mul]
    rfl
  unfold evaluate
  rw [ht]
  exact Summable.tsum_add (summable_evaluationTerms σ K B b hb f)
    (summable_evaluationTerms σ K B b hb g)

omit [IsUltrametricDist B] [CompleteSpace B] in
theorem evaluate_monomial (b : σ → B) (d : σ →₀ ℕ) (a : K) :
    evaluate σ K B b (monomial σ K d a) = algebraMap K B a * monomialValue σ B b d := by
  classical
  unfold evaluate evaluationTerm
  change (∑' e, algebraMap K B (MvPowerSeries.coeff e (MvPowerSeries.monomial d a)) *
    monomialValue σ B b e) = _
  simp only [MvPowerSeries.coeff_monomial, apply_ite, map_zero, zero_mul, ite_mul, tsum_ite_eq]

omit [IsUltrametricDist B] [CompleteSpace B] in
theorem evaluate_algebraMap (b : σ → B) (a : K) :
    evaluate σ K B b (algebraMap K (StrictTateAlgebra σ K) a) = algebraMap K B a := by
  change evaluate σ K B b (monomial σ K 0 a) = _
  rw [evaluate_monomial]
  simp [monomialValue]

theorem evaluate_mul (b : σ → B) (hb : HasBoundedMonomials σ B b)
    (f g : StrictTateAlgebra σ K) :
    evaluate σ K B b (f * g) = evaluate σ K B b f * evaluate σ K B b g := by
  classical
  let : NonarchimedeanRing B :=
    { is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }
  have hf := summable_evaluationTerms σ K B b hb f
  have hg := summable_evaluationTerms σ K B b hb g
  unfold evaluate
  rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg (hf.mul_of_nonarchimedean hg)]
  apply tsum_congr
  intro d
  change algebraMap K B (MvPowerSeries.coeff d (f.val * g.val)) *
    monomialValue σ B b d = _
  rw [MvPowerSeries.coeff_mul, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [map_mul, ← hsum, monomialValue_add]
  exact mul_mul_mul_comm _ _ _ _

/-- The bounded algebra homomorphism defined by a tuple with bounded monomials.
The target may have an unnormalized unit norm, and may be the zero algebra. -/
def evaluateHom (b : σ → B) (hb : HasBoundedMonomials σ B b) :
    BoundedAlgHom K (StrictTateAlgebra σ K) B where
  toFun := evaluate σ K B b
  map_zero' := by
    simpa only [map_zero] using evaluate_algebraMap σ K B b (0 : K)
  map_one' := by
    simpa only [map_one] using evaluate_algebraMap σ K B b (1 : K)
  map_add' := evaluate_add σ K B b hb
  map_mul' := evaluate_mul σ K B b hb
  commutes' := evaluate_algebraMap σ K B b
  bounded := by
    obtain ⟨C, hCpos, hC⟩ := hb
    exact ⟨max 1 ‖(1 : B)‖ * C,
      mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hCpos,
      evaluate_norm_le_bound σ K B b C hC⟩

end Langlands.Analytic.StrictTateAlgebra
