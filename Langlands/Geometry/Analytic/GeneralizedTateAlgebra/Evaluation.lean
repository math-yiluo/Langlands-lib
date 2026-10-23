import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.EvaluationStatement
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.PolynomialApproximation
import Langlands.Geometry.Analytic.TateUniversal.Definitions

/-! # Weighted evaluation and the bounded universal property -/

noncomputable section

universe u v w

namespace Langlands.Analytic.GeneralizedTateAlgebra

open Filter
open scoped Topology

variable {σ : Type u} (r : PositivePolyradius σ) (K : Type v) (B : Type w)
  [NormedField K] [IsUltrametricDist K]
  [NormedCommRing B] [NormedAlgebra K B]

/-- Scalar multiplication gives the exact supplied weighted monomial bound. -/
theorem evaluationTerm_norm_le_bound (b : σ → B) (C : ℝ)
    (hC : ∀ d : σ →₀ ℕ,
      ‖StrictTateAlgebra.monomialValue σ B b d‖ ≤ C * r.weight d)
    (f : GeneralizedTateAlgebra r K) (d : σ →₀ ℕ) :
    ‖evaluationTerm r K B b f d‖ ≤
      C * (‖MvPowerSeries.coeff d (series r K f)‖ * r.weight d) := by
  unfold evaluationTerm
  rw [← Algebra.smul_def]
  calc
    _ ≤ ‖MvPowerSeries.coeff d (series r K f)‖ *
        ‖StrictTateAlgebra.monomialValue σ B b d‖ := norm_smul_le _ _
    _ ≤ ‖MvPowerSeries.coeff d (series r K f)‖ * (C * r.weight d) :=
      mul_le_mul_of_nonneg_left (hC d) (norm_nonneg _)
    _ = _ := by ring

section CompleteTarget

variable [IsUltrametricDist B] [CompleteSpace B]

/-- Weighted coefficient decay implies unconditional convergence in the target. -/
theorem summable_evaluationTerms (b : σ → B) (hb : HasBoundedMonomials r B b)
    (f : GeneralizedTateAlgebra r K) : Summable (evaluationTerm r K B b f) := by
  obtain ⟨C, _, hC⟩ := hb
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (evaluationTerm_norm_le_bound r K B b C hC f)
  have hdecay : Tendsto
      (fun d => ‖MvPowerSeries.coeff d (series r K f)‖ * r.weight d) cofinite (𝓝 0) :=
    f.property
  simpa only [mul_zero] using tendsto_const_nhds.mul hdecay

/-- Evaluation is the sum of its actual evaluated coefficient monomials. -/
theorem hasSum_evaluationTerms (b : σ → B) (hb : HasBoundedMonomials r B b)
    (f : GeneralizedTateAlgebra r K) :
    HasSum (evaluationTerm r K B b f) (evaluate r K B b f) :=
  (summable_evaluationTerms r K B b hb f).hasSum

omit [CompleteSpace B] in
/-- The norm bound uses exactly the supplied constant, including for the zero target. -/
theorem evaluate_norm_le_bound (b : σ → B) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ d : σ →₀ ℕ,
      ‖StrictTateAlgebra.monomialValue σ B b d‖ ≤ C * r.weight d)
    (f : GeneralizedTateAlgebra r K) :
    ‖evaluate r K B b f‖ ≤ C * ‖f‖ :=
  IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg
    (mul_nonneg hCpos.le (norm_nonneg _)) (fun d =>
      (evaluationTerm_norm_le_bound r K B b C hC f d).trans
        (mul_le_mul_of_nonneg_left (weighted_norm_coeff_le r K f d) hCpos.le))

theorem evaluate_add (b : σ → B) (hb : HasBoundedMonomials r B b)
    (f g : GeneralizedTateAlgebra r K) :
    evaluate r K B b (f + g) = evaluate r K B b f + evaluate r K B b g := by
  have ht : evaluationTerm r K B b (f + g) =
      fun d => evaluationTerm r K B b f d + evaluationTerm r K B b g d := by
    funext d
    change algebraMap K B (MvPowerSeries.coeff d (f.val + g.val)) * _ = _
    rw [map_add, map_add, add_mul]
    rfl
  unfold evaluate
  rw [ht]
  exact Summable.tsum_add (summable_evaluationTerms r K B b hb f)
    (summable_evaluationTerms r K B b hb g)

end CompleteTarget

/-- A single monomial evaluates by the finite coordinate product. -/
theorem evaluate_monomial (b : σ → B) (d : σ →₀ ℕ) (a : K) :
    evaluate r K B b (monomial r K d a) =
      algebraMap K B a * StrictTateAlgebra.monomialValue σ B b d := by
  classical
  unfold evaluate evaluationTerm
  change (∑' e, algebraMap K B (MvPowerSeries.coeff e (MvPowerSeries.monomial d a)) *
    StrictTateAlgebra.monomialValue σ B b e) = _
  simp only [MvPowerSeries.coeff_monomial, apply_ite, map_zero, zero_mul, ite_mul,
    tsum_ite_eq]

theorem evaluate_algebraMap (b : σ → B) (a : K) :
    evaluate r K B b (algebraMap K (GeneralizedTateAlgebra r K) a) =
      algebraMap K B a := by
  have h : algebraMap K (GeneralizedTateAlgebra r K) a = monomial r K 0 a := by
    apply Subtype.ext
    exact (MvPowerSeries.monomial_zero_eq_C_apply a).symm
  rw [h, evaluate_monomial]
  simp [StrictTateAlgebra.monomialValue]

theorem evaluate_X (b : σ → B) (i : σ) :
    evaluate r K B b (X r K i) = b i := by
  classical
  rw [X, evaluate_monomial, map_one, one_mul]
  simp [StrictTateAlgebra.monomialValue, Finsupp.prod_single_index]

section CompleteTarget

variable [IsUltrametricDist B] [CompleteSpace B]

/-- Multiplicativity follows from the nonarchimedean Cauchy product. -/
theorem evaluate_mul (b : σ → B) (hb : HasBoundedMonomials r B b)
    (f g : GeneralizedTateAlgebra r K) :
    evaluate r K B b (f * g) = evaluate r K B b f * evaluate r K B b g := by
  classical
  let : NonarchimedeanRing B :=
    { is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean }
  have hf := summable_evaluationTerms r K B b hb f
  have hg := summable_evaluationTerms r K B b hb g
  unfold evaluate
  rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg (hf.mul_of_nonarchimedean hg)]
  apply tsum_congr
  intro d
  change algebraMap K B (MvPowerSeries.coeff d (f.val * g.val)) *
    StrictTateAlgebra.monomialValue σ B b d = _
  rw [MvPowerSeries.coeff_mul, map_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum : ij.1 + ij.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hm : StrictTateAlgebra.monomialValue σ B b (ij.1 + ij.2) =
      StrictTateAlgebra.monomialValue σ B b ij.1 *
        StrictTateAlgebra.monomialValue σ B b ij.2 :=
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
  rw [map_mul, ← hsum, hm]
  exact mul_mul_mul_comm _ _ _ _

/-- Actual weighted evaluation as a bounded algebra homomorphism. -/
def evaluateHom (b : σ → B) (hb : HasBoundedMonomials r B b) :
    BoundedAlgHom K (GeneralizedTateAlgebra r K) B where
  toFun := evaluate r K B b
  map_zero' := by simpa only [map_zero] using evaluate_algebraMap r K B b (0 : K)
  map_one' := by simpa only [map_one] using evaluate_algebraMap r K B b (1 : K)
  map_add' := evaluate_add r K B b hb
  map_mul' := evaluate_mul r K B b hb
  commutes' := evaluate_algebraMap r K B b
  bounded := by
    obtain ⟨C, hCpos, hC⟩ := hb
    exact ⟨C, hCpos, evaluate_norm_le_bound r K B b C hCpos hC⟩

end CompleteTarget

/-- Every source monomial is its coefficient times the finite coordinate product. -/
theorem monomial_eq (d : σ →₀ ℕ) (a : K) :
    monomial r K d a = algebraMap K (GeneralizedTateAlgebra r K) a *
      StrictTateAlgebra.monomialValue σ (GeneralizedTateAlgebra r K) (X r K) d := by
  apply Subtype.ext
  change MvPowerSeries.monomial d a =
    MvPowerSeries.C a * (weightedRestrictedSubalgebra r K).val
      (d.prod fun i n =>
        (⟨(X r K i).val, (X r K i).property⟩ : weightedRestrictedSubalgebra r K) ^ n)
  rw [map_finsuppProd]
  simp only [map_pow]
  exact MvPowerSeries.monomial_eq' d a

theorem map_monomial (φ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B)
    (d : σ →₀ ℕ) (a : K) :
    φ (monomial r K d a) = algebraMap K B a *
      StrictTateAlgebra.monomialValue σ B (fun i => φ (X r K i)) d := by
  rw [monomial_eq]
  change φ.toAlgHom (_ * _) = _
  rw [map_mul, AlgHom.commutes]
  congr 1
  unfold StrictTateAlgebra.monomialValue
  rw [map_finsuppProd]
  simp only [map_pow]

/-- The coordinate monomial bound is inherited from the bound of the homomorphism. -/
theorem hasBoundedMonomials_map_X (φ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B) :
    HasBoundedMonomials r B (fun i => φ (X r K i)) := by
  obtain ⟨C, hCpos, hC⟩ := φ.bounded
  refine ⟨C, hCpos, fun d => ?_⟩
  have heq : StrictTateAlgebra.monomialValue σ B (fun i => φ (X r K i)) d =
      φ (monomial r K d 1) := by
    rw [map_monomial, map_one, one_mul]
  rw [heq]
  have h := hC (monomial r K d 1)
  change ‖φ (monomial r K d 1)‖ ≤ C * ‖monomial r K d 1‖ at h
  simpa only [norm_monomial, norm_one, one_mul] using h

/-- Continuity transports the source expansion, without any completeness assumptions. -/
theorem map_eq_evaluate (φ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B)
    (f : GeneralizedTateAlgebra r K) :
    φ f = evaluate r K B (fun i => φ (X r K i)) f := by
  calc
    φ f = φ (∑' d, monomial r K d (MvPowerSeries.coeff d (series r K f))) :=
      congrArg φ (hasSum_monomials r K f).tsum_eq.symm
    _ = ∑' d, φ (monomial r K d (MvPowerSeries.coeff d (series r K f))) :=
      φ.toContinuousLinearMap.map_tsum (hasSum_monomials r K f).summable
    _ = _ := by
      apply tsum_congr
      intro d
      exact map_monomial r K B φ d _

/-- Coordinate images determine a bounded algebra map into any normed target. -/
theorem hom_ext (φ ψ : BoundedAlgHom K (GeneralizedTateAlgebra r K) B)
    (h : ∀ i, φ (X r K i) = ψ (X r K i)) : φ = ψ := by
  apply BoundedAlgHom.ext
  intro f
  rw [map_eq_evaluate, map_eq_evaluate]
  congr 1
  exact funext h

/-- The full unchanged weighted evaluation and universal-property statement. -/
theorem boundedUniversalProperty : BoundedUniversalPropertyStatement.{u, v, w} := by
  refine ⟨?_, ?_, ?_⟩
  · intro σ r K _ _ B _ _ _ _ b hb
    refine ⟨hasSum_evaluationTerms r K B b hb,
      evaluate_norm_le_bound r K B b, evaluateHom r K B b hb, ?_, ?_⟩
    · intro f
      rfl
    · exact evaluate_X r K B b
  · intro σ r K _ _ B _ _
    exact ⟨hasBoundedMonomials_map_X r K B, hom_ext r K B⟩
  · intro σ r K _ _ B _ _ _ _ b
    constructor
    · intro hb
      refine ⟨evaluateHom r K B b hb, evaluate_X r K B b, ?_⟩
      intro φ hφ
      apply hom_ext r K B
      intro i
      exact (hφ i).trans (evaluate_X r K B b i).symm
    · rintro ⟨φ, hφ, _⟩
      have h := hasBoundedMonomials_map_X r K B φ
      simpa only [hφ] using h

end Langlands.Analytic.GeneralizedTateAlgebra
