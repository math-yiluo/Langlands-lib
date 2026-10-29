import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-!
# Integration over a factorization `G = ι(X) K`

A left-invariant measure on a group `G` is recovered from a measure on a
parameter space `X` and its restriction to a subgroup `K`, whenever every
element of `G` is `ι x * k` with `k ∈ K` and left translation by every `ι x`
is represented by a measure-preserving map of `X`. The proof is a Tonelli
argument; it needs no quotient measure and no compactness.
-/

noncomputable section

namespace Langlands.CompactFactorization

open MeasureTheory Measure Set
open scoped ENNReal

variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  [MeasurableSpace X]

/-- **Factorization integral.** The `K`-restricted integral of `ρ`-integrals of
translates `F (ι x * k)` equals the mass `ρ (ι ⁻¹' K)` times the full integral. -/
theorem lintegral_restrict_lintegral_mul (μ : Measure G) [SFinite μ] [IsMulLeftInvariant μ]
    (K : Subgroup G) (hK : MeasurableSet (K : Set G))
    (ρ : Measure X) [SFinite ρ] (ι : X → G) (hι : Measurable ι)
    (hfac : ∀ y : G, ∃ x₀ : X, ∃ k₀ ∈ K, y = ι x₀ * k₀)
    (hσ : ∀ x₀ : X, ∃ σ : X → X, MeasurePreserving σ ρ ρ ∧
      ∀ x, ι (σ x) = (ι x₀)⁻¹ * ι x)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ k in (K : Set G), ∫⁻ x, F (ι x * k) ∂ρ ∂μ = ρ (ι ⁻¹' K) * ∫⁻ y, F y ∂μ := by
  -- the set of pairs `(x, y)` with `(ι x)⁻¹ * y ∈ K`
  have hpair : Measurable fun p : X × G => (ι p.1)⁻¹ * p.2 :=
    (hι.comp measurable_fst).inv.mul measurable_snd
  have hS : MeasurableSet {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K} := hpair hK
  -- first swap: integrate over `K` inside
  have h1 : ∫⁻ k in (K : Set G), ∫⁻ x, F (ι x * k) ∂ρ ∂μ =
      ∫⁻ x, ∫⁻ k in (K : Set G), F (ι x * k) ∂μ ∂ρ := by
    apply lintegral_lintegral_swap
    exact (hF.comp ((hι.comp measurable_snd).mul measurable_fst)).aemeasurable
  -- left translation by `ι x` turns the `K`-integral into an integral over all of `G`
  have h2 (x : X) : ∫⁻ k in (K : Set G), F (ι x * k) ∂μ =
      ∫⁻ y, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K}.indicator (fun p => F p.2) (x, y) ∂μ := by
    rw [← lintegral_indicator hK]
    rw [← lintegral_mul_left_eq_self _ (ι x)⁻¹]
    apply lintegral_congr
    intro y
    by_cases hy : (ι x)⁻¹ * y ∈ K
    · rw [indicator_of_mem hy, indicator_of_mem (show (x, y) ∈
        {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K} from hy), mul_inv_cancel_left]
    · rw [indicator_of_notMem hy, indicator_of_notMem (show (x, y) ∉
        {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K} from hy)]
  -- second swap: integrate over the parameter space inside
  have h3 : ∫⁻ x, ∫⁻ y, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K}.indicator
        (fun p => F p.2) (x, y) ∂μ ∂ρ =
      ∫⁻ y, ∫⁻ x, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K}.indicator
        (fun p => F p.2) (x, y) ∂ρ ∂μ := by
    apply lintegral_lintegral_swap
    exact ((hF.comp measurable_snd).indicator hS).aemeasurable
  -- the inner parameter integral is the constant mass
  have h4 (y : G) : ∫⁻ x, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K}.indicator
        (fun p => F p.2) (x, y) ∂ρ = ρ (ι ⁻¹' K) * F y := by
    obtain ⟨x₀, k₀, hk₀, rfl⟩ := hfac y
    obtain ⟨σ, hσm, hσι⟩ := hσ x₀
    have hset : {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K} = σ ⁻¹' (ι ⁻¹' K) := by
      ext x
      simp only [mem_ofPred_eq, mem_preimage, SetLike.mem_coe, hσι]
      rw [← mul_assoc, Subgroup.mul_mem_cancel_right K hk₀, ← inv_mem_iff (H := K)]
      simp only [mul_inv_rev, inv_inv]
    have hmeas : MeasurableSet {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K} :=
      ((hι.inv.mul_const _) hK)
    calc ∫⁻ x, {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K}.indicator (fun p => F p.2)
            (x, ι x₀ * k₀) ∂ρ
        = ∫⁻ x, {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K}.indicator 1 x * F (ι x₀ * k₀) ∂ρ := by
          apply lintegral_congr
          intro x
          by_cases hx : (ι x)⁻¹ * (ι x₀ * k₀) ∈ K
          · rw [indicator_of_mem (show (x, ι x₀ * k₀) ∈
              {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K} from hx),
              indicator_of_mem (show x ∈ {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K} from hx),
              Pi.one_apply, one_mul]
          · rw [indicator_of_notMem (show (x, ι x₀ * k₀) ∉
              {p : X × G | (ι p.1)⁻¹ * p.2 ∈ K} from hx),
              indicator_of_notMem (show x ∉ {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K} from hx),
              zero_mul]
      _ = ρ {x : X | (ι x)⁻¹ * (ι x₀ * k₀) ∈ K} * F (ι x₀ * k₀) := by
          rw [lintegral_mul_const _ (measurable_one.indicator hmeas),
            lintegral_indicator_one hmeas]
      _ = ρ (ι ⁻¹' K) * F (ι x₀ * k₀) := by
          rw [hset, hσm.measure_preimage (hι hK).nullMeasurableSet]
  rw [h1]
  simp_rw [h2]
  rw [h3]
  simp_rw [h4]
  rw [lintegral_const_mul _ hF]

end Langlands.CompactFactorization
