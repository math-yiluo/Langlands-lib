import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # The limits in the proof of Proposition VI.4.1 (constant terms of wave packets)

Waldspurger 2003, proof of Proposition VI.4.1 (printed pp. 306–313). The constant term
`f_ψ^{(P')}(m') = δ_{P'}(m')^{1/2} ∫_{U'} f_ψ(m'u') du'` is computed as a limit over the
exhausting compact subgroups `a^{−n}(H ∩ U')a^n` (formula (1)), and in (ii) as
`X^w = lim_{ε→0} X^w(ε) = lim_{ε→0} Σ_s X^w_s(ε)` with `X^w_s(ε) = ∫_O Y_s(ω, ε) dω`, where
`Y_s(χ_λ, ε) = ζ(λ, ε) y(λ, ε)` with `ζ` bounded (assertion (8)).

This module proves the analytic steps of these limits for abstract data:

* `tendsto_inv_mul_setIntegral_comp`: formula (1), `∫_U F = lim_n c_n^{-1} ∫_H F(e_n(v)) dv` for
  measure-scaling bijections `e_n` with `e_n(H)` increasing to `U`;
* `zetaFactor`, `norm_div_add_ofReal_le_one`, `norm_zetaFactor_le_one`: `|ζ(λ, ε)| ≤ 1` for
  imaginary `⟨λ, α̌⟩` and real `ε`;
* `tendsto_integral_rpow_add_mul`: continuity at `0` of `ε ↦ ∫ δ^{1/2+ε} e`;
* `eq_sum_integral_of_tendsto`: dominated convergence over the orbit, `X^w = Σ_s ∫_O F_s`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Langlands.HarishChandraSchwartz

section Exhaustion

variable {U : Type*} [MeasurableSpace U] {μ : Measure U} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- **Formula (1) of the proof of Proposition VI.4.1**: let `e_n` be measurable bijections of `U`
with `e_n(μ) = c_n μ` (for Waldspurger, `e_n(u') = a^{−n} u' a^n` and `c_n = δ_{P'}(a)^n`), such
that the sets `e_n(H)` increase and exhaust `U`. Then for integrable `F`,
`c_n^{−1} ∫_H F(e_n(v)) dμ(v) → ∫_U F dμ`. -/
theorem tendsto_inv_mul_setIntegral_comp {F : U → E} (hF : Integrable F μ) {H : Set U}
    (hH : MeasurableSet H) (e : ℕ → U ≃ᵐ U) (c : ℕ → ℝ≥0∞) (hc0 : ∀ n, c n ≠ 0)
    (hctop : ∀ n, c n ≠ ∞) (hmap : ∀ n, Measure.map (e n) μ = c n • μ)
    (hmono : Monotone fun n => e n '' H) (hcover : ⋃ n, e n '' H = Set.univ) :
    Tendsto (fun n => (c n).toReal⁻¹ • ∫ v in H, F (e n v) ∂μ) atTop (𝓝 (∫ u, F u ∂μ)) := by
  have key : ∀ n, (c n).toReal⁻¹ • ∫ v in H, F (e n v) ∂μ = ∫ u in e n '' H, F u ∂μ := by
    intro n
    have h1 := setIntegral_map_equiv (μ := μ) (e n) F (e n '' H)
    rw [hmap n, Measure.restrict_smul, integral_smul_measure, (e n).preimage_image] at h1
    have hne : (c n).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0 n, hctop n⟩
    rw [← h1, smul_smul, inv_mul_cancel₀ hne, one_smul]
  simp_rw [key]
  have h := tendsto_setIntegral_of_monotone (μ := μ) (f := F)
    (fun n => (e n).measurableSet_image.mpr hH) hmono (by rw [hcover]; exact hF.integrableOn)
  rwa [hcover, Measure.restrict_univ] at h

end Exhaustion

section Zeta

/-- `|z| ≤ |z + b|` for imaginary `z` and real `b`, so `|z / (z + b)| ≤ 1` (the bound
`|⟨λ, α̌⟩| ⩽ |⟨λ + 2εs^{−1}ρ, α̌⟩|` for `λ ∈ i a_M^*` in the proof of Proposition VI.4.1). -/
theorem norm_div_add_ofReal_le_one {z : ℂ} (hz : z.re = 0) (b : ℝ) :
    ‖z / (z + b)‖ ≤ 1 := by
  by_cases h : z + b = 0
  · rw [h, div_zero, norm_zero]
    exact zero_le_one
  · rw [norm_div, div_le_one (norm_pos_iff.mpr h)]
    have hzb : (z + b).re = b := by simp [hz]
    have him : (z + b).im = z.im := by simp
    rw [← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_sq (norm_nonneg (z + b)),
      Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hz, hzb,
      him]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg b])

/-- Waldspurger's `ζ(λ, ε) = Π_{α ∈ Σ_red(P)} [⟨λ, α̌⟩^{n(α)/2} ⟨λ + 2εs^{−1}ρ, α̌⟩^{−n(α)/2}]`
(proof of Proposition VI.4.1), with `z_α = ⟨λ, α̌⟩`, `b_α = ⟨2εs^{−1}ρ, α̌⟩` and
`k_α = n(α)/2`: the product `Π_{α ∈ s} (z_α / (z_α + b_α))^{k_α}`. -/
def zetaFactor {ι : Type*} (s : Finset ι) (z : ι → ℂ) (b : ι → ℝ) (k : ι → ℕ) : ℂ :=
  ∏ i ∈ s, (z i / (z i + b i)) ^ k i

/-- **`ζ` is bounded** (proof of Proposition VI.4.1, assertion (8)):
`|Π_α (z_α / (z_α + b_α))^{k_α}| ≤ 1` for imaginary `z_α` and real `b_α`. -/
theorem norm_zetaFactor_le_one {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ s, (z i).re = 0) (b : ι → ℝ) (k : ι → ℕ) :
    ‖zetaFactor s z b k‖ ≤ 1 := by
  rw [zetaFactor, norm_prod]
  refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i hi => ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_div_add_ofReal_le_one (hz i hi) (b i))

end Zeta

section Continuity

variable {U : Type*} [MeasurableSpace U] {μ : Measure U}

/-- **Continuity of `X^w(ε)` at `0`** (proof of Proposition VI.4.1: "cette intégrale est
absolument convergente, uniformément en `ε`. La fonction `X^w` est donc continue en `0`"): for
`δ ≥ 0` measurable and `e` with `(δ^{1/2} + δ^{1/2+ε₀}) |e|` integrable,
`ε ↦ ∫ δ^{1/2+ε} e` tends to `∫ δ^{1/2} e` as `ε → 0⁺`. -/
theorem tendsto_integral_rpow_add_mul {δ : U → ℝ} (hδ0 : ∀ u, 0 ≤ δ u) (hδm : Measurable δ)
    {e : U → ℂ} (hem : AEStronglyMeasurable e μ) {ε₀ : ℝ} (hε₀ : 0 < ε₀)
    (hint : Integrable (fun u => (δ u ^ (1 / 2 : ℝ) + δ u ^ (1 / 2 + ε₀)) * ‖e u‖) μ) :
    Tendsto (fun ε : ℝ => ∫ u, ((δ u ^ (1 / 2 + ε) : ℝ) : ℂ) * e u ∂μ) (𝓝[>] 0)
      (𝓝 (∫ u, ((δ u ^ (1 / 2 : ℝ) : ℝ) : ℂ) * e u ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun u => (δ u ^ (1 / 2 : ℝ) + δ u ^ (1 / 2 + ε₀)) * ‖e u‖) ?_ ?_ hint ?_
  · refine Eventually.of_forall fun ε => ?_
    exact ((Complex.continuous_ofReal.measurable.comp
      (hδm.pow_const _)).aestronglyMeasurable).mul hem
  · have hmem : Set.Ioo (0 : ℝ) ε₀ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hε₀
    filter_upwards [hmem] with ε hε
    refine Eventually.of_forall fun u => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hδ0 u) _)]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rcases le_total (δ u) 1 with h1 | h1
    · have : δ u ^ (1 / 2 + ε) ≤ δ u ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge' (hδ0 u) h1 (by norm_num) (by linarith [hε.1])
      linarith [Real.rpow_nonneg (hδ0 u) (1 / 2 + ε₀)]
    · have : δ u ^ (1 / 2 + ε) ≤ δ u ^ (1 / 2 + ε₀) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith [hε.2])
      linarith [Real.rpow_nonneg (hδ0 u) (1 / 2 : ℝ)]
  · refine Eventually.of_forall fun u => ?_
    have hc : ContinuousAt (fun ε : ℝ => δ u ^ (1 / 2 + ε)) 0 := by
      by_cases h0 : δ u = 0
      · have hpos : ∀ᶠ ε : ℝ in 𝓝 0, 0 < 1 / 2 + ε :=
          (continuous_const.add continuous_id).continuousAt.eventually
            (lt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2 + 0))
        refine tendsto_nhds_of_eventually_eq ?_
        filter_upwards [hpos] with ε hε
        rw [h0, Real.zero_rpow hε.ne', Real.zero_rpow (by norm_num)]
      · exact (Real.continuousAt_const_rpow h0).comp
          (continuous_const.add continuous_id).continuousAt
    have hc' : Tendsto (fun ε : ℝ => δ u ^ (1 / 2 + ε)) (𝓝[>] 0) (𝓝 (δ u ^ (1 / 2 : ℝ))) := by
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    exact ((Complex.continuous_ofReal.tendsto _).comp hc').mul_const (e u)

end Continuity

section Assembly

/-- **The last step of Proposition VI.4.1 (ii)** (dominated convergence over the orbit): let
`ν` be a finite measure on the orbit `O`, `Y_s(ω, ε)` bounded by `C` for `0 < ε < ε₀`,
measurable in `ω`, with `Y_s(ω, ε) → F_s(ω)` as `ε → 0⁺` for almost every `ω` (assertion (8)),
and `X(ε) = Σ_s ∫_O Y_s(ω, ε) dω` for `0 < ε < ε₀` with `X(ε) → T` (the continuity of `X^w`
at `0`). Then `T = Σ_s ∫_O F_s dω`. -/
theorem eq_sum_integral_of_tendsto {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsFiniteMeasure ν] {ι : Type*} (S : Finset ι) (Y : ι → Ω → ℝ → ℂ) (F : ι → Ω → ℂ)
    {ε₀ C : ℝ} (hε₀ : 0 < ε₀)
    (hmeas : ∀ i ∈ S, ∀ ε, AEStronglyMeasurable (fun ω => Y i ω ε) ν)
    (hbound : ∀ i ∈ S, ∀ ω ε, ε ∈ Set.Ioo 0 ε₀ → ‖Y i ω ε‖ ≤ C)
    (hlim : ∀ i ∈ S, ∀ᵐ ω ∂ν, Tendsto (Y i ω) (𝓝[>] 0) (𝓝 (F i ω))) {X : ℝ → ℂ} {T : ℂ}
    (hX : ∀ ε ∈ Set.Ioo 0 ε₀, X ε = ∑ i ∈ S, ∫ ω, Y i ω ε ∂ν)
    (hT : Tendsto X (𝓝[>] 0) (𝓝 T)) :
    T = ∑ i ∈ S, ∫ ω, F i ω ∂ν := by
  have hmem : Set.Ioo (0 : ℝ) ε₀ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hε₀
  have hi : ∀ i ∈ S, Tendsto (fun ε => ∫ ω, Y i ω ε ∂ν) (𝓝[>] 0) (𝓝 (∫ ω, F i ω ∂ν)) := by
    intro i hiS
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C)
      (Eventually.of_forall fun ε => hmeas i hiS ε) ?_ (integrable_const C) (hlim i hiS)
    filter_upwards [hmem] with ε hε
    exact Eventually.of_forall fun ω => hbound i hiS ω ε hε
  have hsum : Tendsto (fun ε => ∑ i ∈ S, ∫ ω, Y i ω ε ∂ν) (𝓝[>] 0)
      (𝓝 (∑ i ∈ S, ∫ ω, F i ω ∂ν)) := tendsto_finsetSum S hi
  have hX' : Tendsto X (𝓝[>] 0) (𝓝 (∑ i ∈ S, ∫ ω, F i ω ∂ν)) := by
    refine hsum.congr' ?_
    filter_upwards [hmem] with ε hε
    exact (hX ε hε).symm
  exact tendsto_nhds_unique hT hX'

end Assembly

end Langlands.HarishChandraSchwartz
