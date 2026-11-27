import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure

/-! # Replacing an integral over `K` by an integral over an open subgroup

Let `G` be a topological group with subgroups `P`, `K` and s-finite measures satisfying
`dg = dp dk`, let `Δ : P → ℝ≥0` be a continuous multiplicative factor with
`μP.map (· * q) = Δ(q) μP`, and let `W` be an open subgroup of `G` on which `Δ` is trivial. If `Φ`
is continuous on `G` with `Φ(h g) = Δ(h) Φ(g)` for `h ∈ P`, every `k ∈ K` with `Φ(k) ≠ 0` lies in
`P W x⁻¹`, and `(p, k) ↦ 1_{W x⁻¹}(p k) Φ(p k)` is integrable, then
`μ_P(P ∩ W) ∫_K Φ = ∫_{W x⁻¹} Φ dg`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory
open scoped ENNReal NNReal

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {P K : Subgroup G} [MeasurableSpace P] [BorelSpace P] [MeasurableSpace K] [BorelSpace K]

omit [MeasurableSpace G] [BorelSpace G] in
/-- The integral `∫_P 1_W(h h₁) Δ(h) dh` does not depend on `h₁`. -/
theorem integral_indicator_mul_modular (μP : Measure P) [SFinite μP] (Δ : P → ℝ≥0)
    (hΔ : ∀ q : P, μP.map (· * q) = (Δ q : ℝ≥0∞) • μP)
    (hΔmul : ∀ a b : P, Δ (a * b) = Δ a * Δ b) (hΔone : Δ 1 = 1) (hΔc : Continuous Δ)
    (W : Subgroup G) (hW : IsOpen (W : Set G)) (hΔW : ∀ h : P, (h : G) ∈ W → Δ h = 1)
    (h₁ : P) :
    ∫ h, ({h : P | (h : G) ∈ W}.indicator (fun _ => (1 : ℂ)) (h * h₁)) * (Δ h : ℂ) ∂μP =
      (μP.real {h : P | (h : G) ∈ W} : ℂ) := by
  have hmeasW : MeasurableSet {h : P | (h : G) ∈ W} :=
    (hW.preimage continuous_subtype_val).measurableSet
  have hmul : Measurable (fun h : P => h * h₁) := measurable_mul_const h₁
  -- `g(h) = 1_W(h) Δ(h h₁⁻¹)`
  let g : P → ℂ := fun h => {h : P | (h : G) ∈ W}.indicator (fun _ => (1 : ℂ)) h *
    (Δ (h * h₁⁻¹) : ℂ)
  have hgm : AEStronglyMeasurable g (μP.map (· * h₁)) := by
    apply Measurable.aestronglyMeasurable
    refine (measurable_const.indicator hmeasW).mul ?_
    exact (Complex.measurable_ofReal.comp (NNReal.continuous_coe.comp
      (hΔc.comp (continuous_id.mul continuous_const))).measurable)
  have h1 : ∫ h, g h ∂(μP.map (· * h₁)) = ∫ h, g (h * h₁) ∂μP :=
    integral_map hmul.aemeasurable hgm
  have h2 : ∫ h, g h ∂(μP.map (· * h₁)) = (μP.real {h : P | (h : G) ∈ W} : ℂ) := by
    rw [hΔ h₁, integral_smul_measure]
    have hg : ∀ h, g h = {h : P | (h : G) ∈ W}.indicator (fun _ => (Δ h₁⁻¹ : ℂ)) h := by
      intro h
      by_cases hh : (h : G) ∈ W
      · simp only [g, Set.indicator_of_mem (show h ∈ {h : P | (h : G) ∈ W} from hh), one_mul,
          hΔmul, hΔW h hh, one_mul]
      · simp only [g, Set.indicator_of_notMem (show h ∉ {h : P | (h : G) ∈ W} from hh),
          zero_mul]
    simp_rw [hg]
    rw [integral_indicator_const _ hmeasW, ENNReal.coe_toReal, Complex.real_smul,
      Complex.real_smul]
    have hinv : ((Δ h₁ : ℝ) : ℂ) * ((Δ h₁⁻¹ : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← NNReal.coe_mul, ← hΔmul, mul_inv_cancel, hΔone]
      simp
    linear_combination (μP.real {h : P | (h : G) ∈ W} : ℂ) * hinv
  rw [← h2, h1]
  apply integral_congr_ae
  filter_upwards with h
  simp only [g, mul_inv_cancel_right]

/-- **The β-identity.** Let `dg = dp dk`, `Δ` continuous and multiplicative with
`μP.map (· * q) = Δ(q) μP` and trivial on the open subgroup `W`, and `Φ` continuous with
`Φ(h g) = Δ(h) Φ(g)` for `h ∈ P`. If every `k ∈ K` with `Φ(k) ≠ 0` lies in `P W x⁻¹` and the
integrand is integrable, then `μ_P(P ∩ W) ∫_K Φ = ∫_{W x⁻¹} Φ`. -/
theorem integral_indicator_eq_of_iwasawa [SecondCountableTopology P] [SecondCountableTopology K]
    (μG : Measure G) (μP : Measure P) (μK : Measure K) [SFinite μP] [SFinite μK]
    (hIw : μG = (μP.prod μK).map (fun y => (y.1 : G) * y.2))
    (Δ : P → ℝ≥0) (hΔ : ∀ q : P, μP.map (· * q) = (Δ q : ℝ≥0∞) • μP)
    (hΔmul : ∀ a b : P, Δ (a * b) = Δ a * Δ b) (hΔone : Δ 1 = 1) (hΔc : Continuous Δ)
    (W : Subgroup G) (hW : IsOpen (W : Set G)) (hΔW : ∀ h : P, (h : G) ∈ W → Δ h = 1)
    (Φ : G → ℂ) (hΦc : Continuous Φ) (hΦ : ∀ (h : P) (g : G), Φ (h * g) = (Δ h : ℂ) * Φ g)
    (x : G) (hrel : ∀ k : K, Φ k ≠ 0 → ∃ h : P, ∃ w ∈ W, (k : G) = h * w * x⁻¹)
    (hint : Integrable (fun y : P × K =>
      {g : G | g * x ∈ W}.indicator Φ ((y.1 : G) * y.2)) (μP.prod μK)) :
    (μP.real {h : P | (h : G) ∈ W} : ℂ) * ∫ k, Φ k ∂μK =
      ∫ g, {g : G | g * x ∈ W}.indicator Φ g ∂μG := by
  have hS : MeasurableSet {g : G | g * x ∈ W} :=
    (hW.preimage (continuous_id.mul continuous_const)).measurableSet
  have hmulm : Measurable (fun y : P × K => (y.1 : G) * y.2) :=
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).measurable
  rw [hIw, integral_map hmulm.aemeasurable
    (hΦc.measurable.indicator hS).aestronglyMeasurable, integral_prod_symm _ hint,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with k
  by_cases hk : Φ k = 0
  · rw [hk, mul_zero]
    symm
    apply integral_eq_zero_of_ae
    filter_upwards with h
    by_cases hS' : (h : G) * k ∈ {g : G | g * x ∈ W}
    · rw [Set.indicator_of_mem hS', hΦ, hk, mul_zero]
      rfl
    · rw [Set.indicator_of_notMem hS']
      rfl
  obtain ⟨h₁, w₁, hw₁, hk₁⟩ := hrel k hk
  have hpt : ∀ h : P, {g : G | g * x ∈ W}.indicator Φ ((h : G) * k) =
      ({h : P | (h : G) ∈ W}.indicator (fun _ => (1 : ℂ)) (h * h₁)) * (Δ h : ℂ) * Φ k := by
    intro h
    have hiff : (h : G) * k ∈ {g : G | g * x ∈ W} ↔ h * h₁ ∈ {h : P | (h : G) ∈ W} := by
      simp only [Set.mem_ofPred_eq, hk₁, Subgroup.coe_mul]
      rw [show (h : G) * ((h₁ : G) * w₁ * x⁻¹) * x = (h : G) * h₁ * w₁ by group]
      exact ⟨fun hm => by simpa using W.mul_mem hm (W.inv_mem hw₁),
        fun hm => W.mul_mem hm hw₁⟩
    by_cases hm : h * h₁ ∈ {h : P | (h : G) ∈ W}
    · rw [Set.indicator_of_mem (hiff.mpr hm), Set.indicator_of_mem hm, hΦ, one_mul]
    · rw [Set.indicator_of_notMem (fun h' => hm (hiff.mp h')), Set.indicator_of_notMem hm,
        zero_mul, zero_mul]
  simp_rw [hpt]
  rw [integral_mul_const, integral_indicator_mul_modular μP Δ hΔ hΔmul hΔone hΔc W hW hΔW h₁]

end Langlands.BaseChange.TwistedLocalDescent
