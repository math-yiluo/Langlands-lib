import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # Oscillatory terms tested inside their smooth parameter domain -/

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff FourierTransform SchwartzMap Topology

set_option autoImplicit false

namespace Langlands.Analysis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

private theorem exists_fourierPhase_bound {U : Set V} (hU : IsOpen U)
    {a c : V → ℂ} (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (has : tsupport a ⊆ U) (hc : ContDiffOn ℝ ∞ c U) (m : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ ξ : V, ‖ξ‖ ^ m *
      ‖∫ y, Complex.exp (((2 * Real.pi * inner ℝ y ξ : ℝ) : ℂ) * Complex.I) *
        (a y * c y)‖ ≤ M := by
  let f : V → ℂ := fun y => a y * c y
  have hfc : HasCompactSupport f := hac.mul_right
  have hfs : ContDiff ℝ ∞ f := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport a
    · exact ha.contDiffAt.mul (hc.contDiffAt (hU.mem_nhds (has hy)))
    · have heq : f =ᶠ[𝓝 y] fun _ => (0 : ℂ) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hy] with z hz
        simp [f, hz]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  let g : 𝓢(V, ℂ) := hfc.toSchwartzMap hfs
  obtain ⟨M, hM, hbound⟩ := (𝓕⁻ g).decay m 0
  refine ⟨M, hM, fun ξ => ?_⟩
  simpa only [norm_iteratedFDeriv_zero, SchwartzMap.fourierInv_coe, Real.fourierInv_eq',
    smul_eq_mul, g, HasCompactSupport.toSchwartzMap_toFun, f] using hbound ξ

/-- A finite sum of tested Fourier phases tends to zero if the phase vectors grow at least
linearly in the scale and the outside factors grow at most polynomially. The smooth amplitude
of each term is required only on the open set containing the test's support. -/
def SchwartzFourierOscillationStatement : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {A ι : Type*} [Fintype ι]
    (l : Filter A) (r : A → ℝ) (U : Set V) (a : V → ℂ) (c : ι → V → ℂ)
    (ξ : ι → A → V) (b : ι → A → ℂ),
    IsOpen U → ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ U →
    (∀ i, ContDiffOn ℝ ∞ (c i) U) →
    Tendsto r l atTop →
    (∀ i, ∃ (κ B : ℝ) (d : ℕ), 0 < κ ∧ 0 ≤ B ∧
      ∀ᶠ t in l, κ * r t ≤ ‖ξ i t‖ ∧ ‖b i t‖ ≤ B * r t ^ d) →
    Tendsto (fun t => ∑ i, b i t *
      ∫ y, Complex.exp (((2 * Real.pi * inner ℝ y (ξ i t) : ℝ) : ℂ) * Complex.I) *
        (a y * c i y)) l (𝓝 0)

theorem schwartzFourierOscillation : SchwartzFourierOscillationStatement := by
  intro V _ _ _ _ _ A ι _ l r U a c ξ b hU ha hac has hc hr hGrowth
  let I (i : ι) (t : A) : ℂ :=
    ∫ y, Complex.exp (((2 * Real.pi * inner ℝ y (ξ i t) : ℝ) : ℂ) * Complex.I) *
      (a y * c i y)
  have hterm (i : ι) : Tendsto (fun t => b i t * I i t) l (𝓝 0) := by
    obtain ⟨κ, B, d, hκ, hB, hg⟩ := hGrowth i
    obtain ⟨M, _, hM⟩ := exists_fourierPhase_bound hU ha hac has (hc i) (d + 1)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdecay : Tendsto (fun t => (B * M / κ ^ (d + 1)) / r t) l (𝓝 0) :=
      tendsto_const_nhds.div_atTop hr
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hdecay
    filter_upwards [hg, hr.eventually_gt_atTop 0] with t ht htpos
    have hpow : (κ * r t) ^ (d + 1) ≤ ‖ξ i t‖ ^ (d + 1) :=
      pow_le_pow_left₀ (mul_nonneg hκ.le htpos.le) ht.1 _
    have hI : (κ * r t) ^ (d + 1) * ‖I i t‖ ≤ M :=
      (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans (hM (ξ i t))
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)).trans ?_
    rw [div_div, le_div_iff₀ (mul_pos (pow_pos hκ _) htpos)]
    calc
      _ = B * ((κ * r t) ^ (d + 1) * ‖I i t‖) := by rw [mul_pow, pow_succ (r t)]; ring
      _ ≤ B * M := mul_le_mul_of_nonneg_left hI hB
  simpa only [I, Finset.sum_const_zero] using
    (tendsto_finsetSum Finset.univ (fun i _ => hterm i))

end Langlands.Analysis
