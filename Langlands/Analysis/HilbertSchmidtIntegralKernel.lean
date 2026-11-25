import Langlands.Analysis.OperatorIdeals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Hilbert–Schmidt integral operators have square-integrable kernels

Let `μ` be an s-finite measure on a countably generated measurable space `X`, so that `L²(X, μ)`
is separable. If a Hilbert–Schmidt operator `T` on `L²(X, μ)` is given by a kernel `K` that is
almost everywhere strongly measurable on `X × X` and has square-integrable rows `K(x, ·)` for almost
every `x`, `(T φ)(x) = ∫ K(x, y) φ(y) dμ(y)` almost everywhere for every `φ`, then
`K ∈ L²(X × X, μ × μ)` (`memLp_uncurry_of_isHilbertSchmidt`): for a Hilbert basis `(e_i)`, which is
countable (`countable_of_hilbertBasis`), Parseval's identity for the rows and
Tonelli's theorem give `∫∫ |K|² = Σ_i ‖T e_i‖² < ∞`.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace Langlands.Analysis.OperatorIdeals

/-- The index type of a Hilbert basis of a separable inner product space is countable: the open
balls of radius `1 / 2` about the basis vectors are pairwise disjoint, as distinct basis vectors are
at distance `√2`. -/
theorem countable_of_hilbertBasis {ι 𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [TopologicalSpace.SeparableSpace E]
    (b : HilbertBasis ι 𝕜 E) : Countable ι := by
  refine Pairwise.countable_of_isOpen_disjoint (s := fun i => Metric.ball (b i) (1 / 2))
    (fun i j hij => ?_) (fun _ => Metric.isOpen_ball)
    (fun i => ⟨b i, Metric.mem_ball_self (by norm_num)⟩)
  rw [Function.onFun, Set.disjoint_left]
  intro z hzi hzj
  have hd : dist (b i) (b j) < 1 := by
    calc dist (b i) (b j) ≤ dist (b i) z + dist z (b j) := dist_triangle _ _ _
      _ < 1 / 2 + 1 / 2 := add_lt_add (by rw [dist_comm]; exact hzi) hzj
      _ = 1 := by norm_num
  have hsq : ‖b i - b j‖ ^ 2 = 2 := by
    rw [@norm_sub_sq 𝕜, b.orthonormal.1 i, b.orthonormal.1 j, b.orthonormal.2 hij]
    simp; norm_num
  rw [dist_eq_norm] at hd
  nlinarith [norm_nonneg (b i - b j)]

private lemma lintegral_enorm_sq_L2 {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (g : Lp ℂ 2 μ) : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (‖g‖ ^ 2) := by
  have hi : Integrable (fun x => ‖g x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp g).aestronglyMeasurable).1 (Lp.memLp g)
  have he : ∫ x, ‖g x‖ ^ 2 ∂μ = ‖g‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner g g)]
    simp only [← norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [← he, ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun _ => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- **A Hilbert–Schmidt integral operator with square-integrable rows has a square-integrable
kernel.** On a countably generated measurable space with an s-finite measure `μ`, let `T` be a
Hilbert–Schmidt operator on `L²(X, μ)` and `K : X → X → ℂ` almost everywhere strongly measurable on
`X × X`, with `K x ∈ L²(μ)` for almost every `x` and `(T φ)(x) = ∫ K(x, y) φ(y) dμ(y)` for almost
every `x`, for every `φ`. Then `K ∈ L²(X × X, μ × μ)`. -/
theorem memLp_uncurry_of_isHilbertSchmidt {X : Type*} [MeasurableSpace X]
    [MeasurableSpace.CountablyGenerated X] {μ : Measure X} [SFinite μ]
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (hT : IsHilbertSchmidt T) (K : X → X → ℂ)
    (hKm : AEStronglyMeasurable (Function.uncurry K) (μ.prod μ))
    (hrow : ∀ᵐ x ∂μ, MemLp (K x) 2 μ)
    (hTK : ∀ φ : Lp ℂ 2 μ, (T φ : X → ℂ) =ᵐ[μ] fun x => ∫ y, K x y * φ y ∂μ) :
    MemLp (Function.uncurry K) 2 (μ.prod μ) := by
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  obtain ⟨s, b, hb⟩ := hT
  have : Countable s := countable_of_hilbertBasis b
  have hae : ∀ᵐ x ∂μ, MemLp (K x) 2 μ ∧
      ∀ i, (T (b i) : X → ℂ) x = ∫ y, K x y * b i y ∂μ :=
    hrow.and (ae_all_iff.2 fun i => hTK (b i))
  have hrowEq : ∀ᵐ x ∂μ, ∫⁻ y, ‖K x y‖ₑ ^ 2 ∂μ = ∑' i, ‖(T (b i) : X → ℂ) x‖ₑ ^ 2 := by
    filter_upwards [hae] with x ⟨hx, hxi⟩
    set r : Lp ℂ 2 μ := hx.star.toLp with hr
    have hrc : (r : X → ℂ) =ᵐ[μ] star (K x) := hx.star.coeFn_toLp
    have hpair (i : s) : inner ℂ r (b i) = (T (b i) : X → ℂ) x := by
      rw [hxi i, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hrc] with y hy
      rw [RCLike.inner_apply, hy]
      simp [mul_comm]
    have hnorm : ∫⁻ y, ‖K x y‖ₑ ^ 2 ∂μ = ENNReal.ofReal (‖r‖ ^ 2) := by
      rw [← lintegral_enorm_sq_L2 r]
      refine lintegral_congr_ae ?_
      filter_upwards [hrc] with y hy
      rw [hy]
      simp
    have hpars : HasSum (fun i => ‖inner ℂ r (b i)‖ ^ 2) (‖r‖ ^ 2) := by
      have h := Complex.reCLM.hasSum (b.hasSum_inner_mul_inner r r)
      have h1 : Complex.reCLM (inner ℂ r r) = ‖r‖ ^ 2 := by
        rw [Complex.reCLM_apply]
        exact inner_self_eq_norm_sq (𝕜 := ℂ) r
      have h2 (i : s) : Complex.reCLM (inner ℂ r (b i) * inner ℂ (b i) r) =
          ‖inner ℂ r (b i)‖ ^ 2 := by
        rw [Complex.reCLM_apply, ← inner_conj_symm (b i) r, RCLike.mul_conj]
        norm_cast
      simp only [h1, h2] at h
      exact h
    rw [hnorm, ← hpars.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
      hpars.summable]
    refine tsum_congr fun i => ?_
    rw [hpair, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have hsum : ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2) < ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hb]
    exact ENNReal.ofReal_lt_top
  rw [memLp_iff,
    eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) ENNReal.ofNat_ne_top hKm]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc ∫⁻ p, ‖Function.uncurry K p‖ₑ ^ 2 ∂(μ.prod μ)
      = ∫⁻ x, ∫⁻ y, ‖K x y‖ₑ ^ 2 ∂μ ∂μ :=
        lintegral_prod _ (hKm.enorm.pow_const 2)
    _ = ∫⁻ x, ∑' i, ‖(T (b i) : X → ℂ) x‖ₑ ^ 2 ∂μ := lintegral_congr_ae hrowEq
    _ = ∑' i, ∫⁻ x, ‖(T (b i) : X → ℂ) x‖ₑ ^ 2 ∂μ :=
        lintegral_tsum fun i => (Lp.aestronglyMeasurable _).enorm.pow_const 2
    _ = ∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2) := tsum_congr fun i => lintegral_enorm_sq_L2 _
    _ < ⊤ := hsum

end Langlands.Analysis.OperatorIdeals
