import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Local bases and the vanishing of `X⁺` (Waldspurger, proof of Proposition VI.4.1)

Abstract forms of the steps of the proof of Proposition VI.4.1 (printed pp. 307–309) that prove
the bound (4) and deduce `X⁺ = 0`: coefficients in a family of vectors that is a basis at one
point are bounded, near that point, by the inner products with the family; a bound valid near
every point of a compact set is uniform on it; and the resulting bound makes the normalized
integrals defining `X⁺` tend to zero.
-/

namespace Langlands.HarishChandraSchwartz

open Filter Topology MeasureTheory

section Coefficients

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {ι : Type*} [Fintype ι]

/-- Quantitative openness of linear independence: near a linearly independent finite family,
the coefficients of a linear combination are bounded by the norm of the combination,
uniformly. -/
theorem exists_norm_le_norm_sum_smul_of_linearIndependent {f : ι → E}
    (hf : LinearIndependent 𝕜 f) :
    ∃ C > 0, ∀ᶠ g in 𝓝 f, ∀ c : ι → 𝕜, ‖c‖ ≤ C * ‖∑ i, c i • g i‖ := by
  obtain ⟨K, K0, hK⟩ := LinearMap.exists_antilipschitzWith (Fintype.linearCombination 𝕜 f)
    (LinearMap.ker_eq_bot.2 hf.fintypeLinearCombination_injective)
  have hK0 : (0 : ℝ) < K := K0
  have hKc : ∀ c : ι → 𝕜, ‖c‖ ≤ K * ‖∑ i, c i • f i‖ := by
    intro c
    have h := hK.mul_le_dist c 0
    simp only [dist_zero_right, map_zero, Fintype.linearCombination_apply] at h
    push_cast at h
    calc ‖c‖ = (K : ℝ) * ((K : ℝ)⁻¹ * ‖c‖) := by field_simp
      _ ≤ K * ‖∑ i, c i • f i‖ := mul_le_mul_of_nonneg_left h hK0.le
  have hT : Tendsto (fun g : ι → E => ∑ i, ‖g i - f i‖) (𝓝 f) (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ =>
      Tendsto.norm (((continuous_apply i).tendsto f).sub (tendsto_const_nhds (x := f i)))
    simpa using this
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [hT.eventually (gt_mem_nhds (show (0 : ℝ) < (2 * (K : ℝ))⁻¹ by positivity))]
    with g hg c
  set S := ∑ i, ‖g i - f i‖ with hS
  have h1 : ‖∑ i, c i • g i - ∑ i, c i • f i‖ ≤ ‖c‖ * S := by
    rw [← Finset.sum_sub_distrib, hS, Finset.mul_sum]
    refine norm_sum_le_of_le _ fun i _ => ?_
    rw [← smul_sub, norm_smul]
    exact mul_le_mul_of_nonneg_right (norm_le_pi_norm c i) (norm_nonneg _)
  have h2 : ‖∑ i, c i • f i‖ ≤ ‖∑ i, c i • g i‖ + ‖c‖ * S := by
    have := norm_le_norm_add_norm_sub' (∑ i, c i • f i) (∑ i, c i • g i)
    rw [norm_sub_rev] at this
    linarith
  have hKS : (K : ℝ) * S ≤ 1 / 2 := by
    have : S ≤ (2 * (K : ℝ))⁻¹ := hg.le
    calc (K : ℝ) * S ≤ K * (2 * (K : ℝ))⁻¹ := mul_le_mul_of_nonneg_left this hK0.le
      _ = 1 / 2 := by field_simp
  have h3 : ‖c‖ * ((K : ℝ) * S) ≤ ‖c‖ * (1 / 2) :=
    mul_le_mul_of_nonneg_left hKS (norm_nonneg c)
  have h4 := hKc c
  have h5 : (K : ℝ) * ‖∑ i, c i • f i‖ ≤ K * ‖∑ i, c i • g i‖ + ‖c‖ * (K * S) := by
    have := mul_le_mul_of_nonneg_left h2 hK0.le
    linarith
  linarith

end Coefficients

section Inner

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  {ι : Type*} [Fintype ι]

/-- Near a linearly independent finite family `f`, the coefficients of a linear combination of
a family `g` are bounded by the inner products of the combination with the members of `g`
(the constant `C₁` of the proof of Proposition VI.4.1). -/
theorem exists_sum_norm_le_sum_norm_inner_of_linearIndependent {f : ι → E}
    (hf : LinearIndependent 𝕜 f) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ g in 𝓝 f, ∀ c : ι → 𝕜,
      ∑ i, ‖c i‖ ≤ C * ∑ j, ‖inner 𝕜 (g j) (∑ i, c i • g i)‖ := by
  obtain ⟨C, C0, hC⟩ := exists_norm_le_norm_sum_smul_of_linearIndependent hf
  refine ⟨Fintype.card ι * C * C, by positivity, ?_⟩
  filter_upwards [hC] with g hg c
  set w := ∑ i, c i • g i with hw
  set S := ∑ j, ‖inner 𝕜 (g j) w‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hcard : ∑ i, ‖c i‖ ≤ Fintype.card ι * ‖c‖ := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset ι) (fun i => ‖c i‖) ‖c‖
      fun i _ => norm_le_pi_norm c i
    simpa [nsmul_eq_mul] using this
  have hww : ‖w‖ * ‖w‖ ≤ ‖c‖ * S := by
    have h1 : inner 𝕜 w w = ∑ i, c i * inner 𝕜 w (g i) := by
      calc inner 𝕜 w w = inner 𝕜 w (∑ i, c i • g i) := rfl
        _ = ∑ i, c i * inner 𝕜 w (g i) := by
          rw [inner_sum]; simp only [inner_smul_right]
    have h2 : ‖w‖ * ‖w‖ ≤ ‖inner 𝕜 w w‖ := by
      rw [← inner_self_eq_norm_mul_norm (𝕜 := 𝕜)]
      exact RCLike.re_le_norm _
    refine h2.trans ?_
    rw [h1, hS, Finset.mul_sum]
    refine norm_sum_le_of_le _ fun i _ => ?_
    rw [norm_mul, norm_inner_symm]
    exact mul_le_mul_of_nonneg_right (norm_le_pi_norm c i) (norm_nonneg _)
  have hwS : ‖w‖ ≤ C * S := by
    rcases (norm_nonneg w).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · refine le_of_mul_le_mul_left ?_ hpos
      calc ‖w‖ * ‖w‖ ≤ ‖c‖ * S := hww
        _ ≤ (C * ‖w‖) * S := mul_le_mul_of_nonneg_right (hg c) hS0
        _ = ‖w‖ * (C * S) := by ring
  calc ∑ i, ‖c i‖ ≤ Fintype.card ι * ‖c‖ := hcard
    _ ≤ Fintype.card ι * (C * ‖w‖) := by gcongr; exact hg c
    _ ≤ Fintype.card ι * (C * (C * S)) := by gcongr
    _ = Fintype.card ι * C * C * S := by ring

/-- Near a linearly independent finite family `f`, a linear map that is bounded by `B` on the
members of `g` is bounded on the span of `g` by `C * B` times the sum of the inner products
with the members of `g` (inequality (5) of the proof of Proposition VI.4.1). -/
theorem exists_norm_apply_le_of_linearIndependent {F : Type*} [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] {f : ι → E} (hf : LinearIndependent 𝕜 f) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ g in 𝓝 f, ∀ (ℓ : E →ₗ[𝕜] F) (B : ℝ), (∀ i, ‖ℓ (g i)‖ ≤ B) →
      ∀ w ∈ Submodule.span 𝕜 (Set.range g), ‖ℓ w‖ ≤ C * B * ∑ j, ‖inner 𝕜 (g j) w‖ := by
  obtain ⟨C, C0, hC⟩ := exists_sum_norm_le_sum_norm_inner_of_linearIndependent hf
  refine ⟨C, C0, ?_⟩
  filter_upwards [hC] with g hg ℓ B hB w hwg
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).1 hwg
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (Classical.arbitrary ι))
  have h1 : ‖ℓ (∑ i, c i • g i)‖ ≤ B * ∑ i, ‖c i‖ := by
    rw [map_sum, Finset.mul_sum]
    refine norm_sum_le_of_le _ fun i _ => ?_
    rw [map_smul, norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB i) (norm_nonneg _)
  calc ‖ℓ (∑ i, c i • g i)‖ ≤ B * ∑ i, ‖c i‖ := h1
    _ ≤ B * (C * ∑ j, ‖inner 𝕜 (g j) (∑ i, c i • g i)‖) :=
        mul_le_mul_of_nonneg_left (hg c) hB0
    _ = C * B * ∑ j, ‖inner 𝕜 (g j) (∑ i, c i • g i)‖ := by ring

omit [Fintype ι] in
/-- A finite family that is a basis of a finite-dimensional space at one point still spans the
space nearby. -/
theorem eventually_span_eq_top_of_linearIndependent [Finite ι] [FiniteDimensional 𝕜 E]
    {f : ι → E} (hf : LinearIndependent 𝕜 f) (hspan : Submodule.span 𝕜 (Set.range f) = ⊤) :
    ∀ᶠ g in 𝓝 f, Submodule.span 𝕜 (Set.range g) = ⊤ := by
  cases nonempty_fintype ι
  have hcard : Fintype.card ι = Module.finrank 𝕜 E := by
    rw [← finrank_span_eq_card hf, hspan, finrank_top]
  filter_upwards [hf.eventually] with g hg
  exact hg.span_eq_top_of_card_eq_finrank' hcard

/-- Local form of the bound (4) of the proof of Proposition VI.4.1. Let `b` be a family of
vectors of a finite-dimensional inner product space, depending on a parameter `ω`, continuous at
`ω₀` and a basis at `ω₀`. If the linear maps `ℓ n ω` are bounded on the `b ω i` by
`C₂ e^{-ε h(n)}` and the inner products of the `b ω j` with `ψ n ω` are bounded by
`C₄ t(n) (1 + s(n))^d` for `ω` near `ω₀`, then `‖ℓ n ω (ψ n ω)‖` is bounded by
`C t(n) (1 + s(n))^d e^{-ε h(n)}` for `ω` near `ω₀`. -/
theorem exists_local_decay_of_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [FiniteDimensional 𝕜 E] {X : Type*} [TopologicalSpace X] {b : X → ι → E} {ω₀ : X}
    (hb : ContinuousAt b ω₀) (hli : LinearIndependent 𝕜 (b ω₀))
    (hspan : Submodule.span 𝕜 (Set.range (b ω₀)) = ⊤) (ℓ : ℕ → X → E →ₗ[𝕜] F)
    (ψ : ℕ → X → E) (t s h : ℕ → ℝ) {V : Set X} (hV : V ∈ 𝓝 ω₀) {ε C₂ C₄ : ℝ} {d : ℕ}
    (hC₂ : 0 ≤ C₂) (h₂ : ∀ ω ∈ V, ∀ n i, ‖ℓ n ω (b ω i)‖ ≤ C₂ * Real.exp (-(ε * h n)))
    (h₄ : ∀ ω ∈ V, ∀ n j, ‖inner 𝕜 (b ω j) (ψ n ω)‖ ≤ C₄ * t n * (1 + s n) ^ d) :
    ∃ U ∈ 𝓝 ω₀, ∃ C : ℝ, ∀ ω ∈ U, ∀ n,
      ‖ℓ n ω (ψ n ω)‖ ≤ C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n)) := by
  obtain ⟨C, C0, hC⟩ := exists_norm_apply_le_of_linearIndependent (F := F) hli
  have h1 := hb.eventually hC
  have h2 := hb.eventually (eventually_span_eq_top_of_linearIndependent hli hspan)
  refine ⟨{ω | ω ∈ V ∧ (∀ (ℓ : E →ₗ[𝕜] F) (B : ℝ), (∀ i, ‖ℓ (b ω i)‖ ≤ B) →
      ∀ w ∈ Submodule.span 𝕜 (Set.range (b ω)), ‖ℓ w‖ ≤ C * B * ∑ j, ‖inner 𝕜 (b ω j) w‖) ∧
      Submodule.span 𝕜 (Set.range (b ω)) = ⊤}, ?_, C * C₂ * Fintype.card ι * C₄, ?_⟩
  · filter_upwards [hV, h1, h2] with ω hω hω1 hω2 using ⟨hω, hω1, hω2⟩
  rintro ω ⟨hωV, hω1, hω2⟩ n
  have hmem : ψ n ω ∈ Submodule.span 𝕜 (Set.range (b ω)) := by
    rw [hω2]; exact Submodule.mem_top
  have hle := hω1 (ℓ n ω) _ (h₂ ω hωV n) (ψ n ω) hmem
  have hsum : ∑ j, ‖inner 𝕜 (b ω j) (ψ n ω)‖ ≤ Fintype.card ι * (C₄ * t n * (1 + s n) ^ d) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset ι)
      (fun j => ‖inner 𝕜 (b ω j) (ψ n ω)‖) (C₄ * t n * (1 + s n) ^ d)
      fun j _ => h₄ ω hωV n j
    simpa [nsmul_eq_mul] using this
  have hCB : 0 ≤ C * (C₂ * Real.exp (-(ε * h n))) := by positivity
  calc ‖ℓ n ω (ψ n ω)‖ ≤ C * (C₂ * Real.exp (-(ε * h n))) *
        ∑ j, ‖inner 𝕜 (b ω j) (ψ n ω)‖ := hle
    _ ≤ C * (C₂ * Real.exp (-(ε * h n))) * (Fintype.card ι * (C₄ * t n * (1 + s n) ^ d)) :=
        mul_le_mul_of_nonneg_left hsum hCB
    _ = C * C₂ * Fintype.card ι * C₄ * t n * (1 + s n) ^ d * Real.exp (-(ε * h n)) := by ring

end Inner

section Uniform

variable {X : Type*}

/-- `F n ω ≤ C t(n) (1 + s(n))^d e^{-ε h(n)}` for all `ω ∈ S` and all `n`, for some `ε > 0`, `C`
and `d` (the form of the bound (4) of the proof of Proposition VI.4.1, with `t(n) = δ_{P'}(a)^{n/2}`,
`s(n) = σ(a^n)` and `h(n) = |H_0(a^n)|`). -/
def IsDecayBoundedOn (F : ℕ → X → ℝ) (t s h : ℕ → ℝ) (S : Set X) : Prop :=
  ∃ ε > 0, ∃ C : ℝ, ∃ d : ℕ, ∀ ω ∈ S, ∀ n,
    F n ω ≤ C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n))

theorem IsDecayBoundedOn.mono {F : ℕ → X → ℝ} {t s h : ℕ → ℝ} {S T : Set X}
    (hT : IsDecayBoundedOn F t s h T) (hST : S ⊆ T) : IsDecayBoundedOn F t s h S := by
  obtain ⟨ε, hε, C, d, hb⟩ := hT
  exact ⟨ε, hε, C, d, fun ω hω => hb ω (hST hω)⟩

/-- A bound of the form `C t(n) (1 + s(n))^d e^{-ε h(n)}` valid near every point of a compact
set is valid on the whole set with one choice of `ε > 0`, `C` and `d` (the reduction to a
neighbourhood of `ω₀` in the proof of the bound (4) of Proposition VI.4.1). -/
theorem isDecayBoundedOn_of_isCompact [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) (F : ℕ → X → ℝ) (t s h : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n)
    (hs : ∀ n, 0 ≤ s n) (hh : ∀ n, 0 ≤ h n)
    (hloc : ∀ ω₀ ∈ S, ∃ U ∈ 𝓝 ω₀, IsDecayBoundedOn F t s h U) :
    IsDecayBoundedOn F t s h S := by
  have hmono : ∀ {ε₁ ε C₁ C : ℝ} {d₁ d : ℕ}, ε ≤ ε₁ → C₁ ≤ C → 0 ≤ C → d₁ ≤ d →
      ∀ n, C₁ * t n * (1 + s n) ^ d₁ * Real.exp (-(ε₁ * h n)) ≤
        C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n)) := by
    intro ε₁ ε C₁ C d₁ d hε hC hC0 hd n
    have h1 : 1 ≤ 1 + s n := le_add_of_nonneg_right (hs n)
    have hp : (1 + s n) ^ d₁ ≤ (1 + s n) ^ d := pow_le_pow_right₀ h1 hd
    have he : Real.exp (-(ε₁ * h n)) ≤ Real.exp (-(ε * h n)) :=
      Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hε (hh n)))
    have hp0 : 0 ≤ (1 + s n) ^ d₁ := by positivity
    calc C₁ * t n * (1 + s n) ^ d₁ * Real.exp (-(ε₁ * h n))
        ≤ C * t n * (1 + s n) ^ d₁ * Real.exp (-(ε₁ * h n)) := by
          gcongr
          · exact ht n
      _ ≤ C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n)) := by
          have : 0 ≤ C * t n := mul_nonneg hC0 (ht n)
          gcongr
  have key : ∃ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ ω ∈ S, ∀ n,
      F n ω ≤ C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n)) := by
    refine hS.induction_on (p := fun T => ∃ ε > 0, ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ ω ∈ T, ∀ n,
      F n ω ≤ C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n))) ?_ ?_ ?_ ?_
    · exact ⟨1, one_pos, 0, le_rfl, 0, fun ω hω => absurd hω (Set.notMem_empty ω)⟩
    · rintro T₁ T₂ hT ⟨ε, hε, C, hC, d, hb⟩
      exact ⟨ε, hε, C, hC, d, fun ω hω => hb ω (hT hω)⟩
    · rintro T₁ T₂ ⟨ε₁, hε₁, C₁, hC₁, d₁, hb₁⟩ ⟨ε₂, hε₂, C₂, hC₂, d₂, hb₂⟩
      refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, max C₁ C₂, le_max_of_le_left hC₁, max d₁ d₂, ?_⟩
      rintro ω (hω | hω) n
      · exact (hb₁ ω hω n).trans (hmono (min_le_left _ _) (le_max_left _ _)
          (le_max_of_le_left hC₁) (le_max_left _ _) n)
      · exact (hb₂ ω hω n).trans (hmono (min_le_right _ _) (le_max_right _ _)
          (le_max_of_le_left hC₁) (le_max_right _ _) n)
    · intro ω₀ hω₀
      obtain ⟨U, hU, ε, hε, C, d, hb⟩ := hloc ω₀ hω₀
      refine ⟨U, mem_nhdsWithin_of_mem_nhds hU, ε, hε, max C 0, le_max_right _ _, d,
        fun ω hω n => (hb ω hω n).trans (hmono le_rfl (le_max_left _ _) (le_max_right _ _)
          le_rfl n)⟩
  obtain ⟨ε, hε, C, -, d, hb⟩ := key
  exact ⟨ε, hε, C, d, hb⟩

end Uniform

section Limit

/-- `(1 + |A| n)^d e^{-c n} → 0` for `c > 0`. -/
theorem tendsto_one_add_mul_pow_mul_exp_neg (A : ℝ) (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (1 + |A| * n) ^ d * Real.exp (-(c * n))) atTop (𝓝 0) := by
  have hx : Tendsto (fun n : ℕ => c * (1 + (n : ℝ))) atTop atTop :=
    Tendsto.const_mul_atTop hc (tendsto_atTop_add_const_left _ 1 tendsto_natCast_atTop_atTop)
  have hlim := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp hx).const_mul
    ((1 + |A|) ^ d * Real.exp c / c ^ d)
  rw [mul_zero] at hlim
  refine squeeze_zero (fun n => by positivity) (fun n => ?_) hlim
  have hcd : 0 < c ^ d := pow_pos hc d
  have h1 : 1 + |A| * n ≤ (1 + |A|) * (1 + n) := by
    have : 0 ≤ |A| * n := by positivity
    nlinarith [abs_nonneg A, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : (1 + |A| * n) ^ d ≤ (1 + |A|) ^ d * (1 + n) ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 d
  have h3 : (1 + |A|) ^ d * Real.exp c / c ^ d * ((c * (1 + n)) ^ d * Real.exp (-(c * (1 + n))))
      = (1 + |A|) ^ d * (1 + n) ^ d * Real.exp (-(c * n)) := by
    rw [mul_pow]
    have : Real.exp c * Real.exp (-(c * (1 + n))) = Real.exp (-(c * n)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc (1 + |A|) ^ d * Real.exp c / c ^ d * (c ^ d * (1 + n) ^ d * Real.exp (-(c * (1 + n))))
        = (1 + |A|) ^ d * (1 + n) ^ d * (Real.exp c * Real.exp (-(c * (1 + n)))) *
            (c ^ d / c ^ d) := by ring
      _ = (1 + |A|) ^ d * (1 + n) ^ d * Real.exp (-(c * n)) := by
          rw [this, div_self hcd.ne', mul_one]
  simp only [Function.comp_apply]
  rw [h3]
  exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

/-- The vanishing of `X⁺` in the proof of Proposition VI.4.1: if `‖F n ω‖` is bounded by
`C t(n) (1 + s(n))^d e^{-ε h(n)}` with `s(n) ≤ A n` and `h(n) ≥ B n`, `B > 0`, then
`t(n)⁻¹ ∫ w(ω) F n ω dμ(ω)` tends to `0` for every integrable `w`. -/
theorem tendsto_inv_smul_integral_of_decay {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {w : X → ℂ} (hw : Integrable w μ) (F : ℕ → X → ℂ) (t s h : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (hs0 : ∀ n, 0 ≤ s n) {A B ε C : ℝ} {d : ℕ} (hB : 0 < B) (hε : 0 < ε)
    (hs : ∀ n, s n ≤ A * n) (hh : ∀ n, B * n ≤ h n)
    (hF : ∀ n, ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n))) :
    Tendsto (fun n => (t n)⁻¹ • ∫ ω, w ω * F n ω ∂μ) atTop (𝓝 0) := by
  have hlim := (tendsto_one_add_mul_pow_mul_exp_neg A d (mul_pos hε hB)).const_mul
    (|C| * ∫ ω, ‖w ω‖ ∂μ)
  rw [mul_zero] at hlim
  refine squeeze_zero_norm (fun n => ?_) hlim
  have htn := ht n
  set K := C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n)) with hK
  have hnorm : ‖∫ ω, w ω * F n ω ∂μ‖ ≤ ∫ ω, ‖w ω‖ * K ∂μ := by
    refine norm_integral_le_of_norm_le (hw.norm.mul_const K) ?_
    filter_upwards [hF n] with ω hω
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hω (norm_nonneg _)
  rw [integral_mul_const] at hnorm
  have hI : 0 ≤ ∫ ω, ‖w ω‖ ∂μ := integral_nonneg fun ω => norm_nonneg _
  have hs1 : (1 + s n) ^ d ≤ (1 + |A| * n) ^ d := by
    refine pow_le_pow_left₀ (by linarith [hs0 n]) ?_ d
    have : A * n ≤ |A| * n := mul_le_mul_of_nonneg_right (le_abs_self A) (Nat.cast_nonneg n)
    linarith [hs n]
  have he : Real.exp (-(ε * h n)) ≤ Real.exp (-(ε * B * n)) := by
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hh n) hε.le
  have hK' : K ≤ |C| * t n * ((1 + |A| * n) ^ d * Real.exp (-(ε * B * n))) := by
    rw [hK]
    calc C * t n * (1 + s n) ^ d * Real.exp (-(ε * h n))
        ≤ |C| * t n * (1 + s n) ^ d * Real.exp (-(ε * h n)) := by
          have : 0 ≤ t n * (1 + s n) ^ d * Real.exp (-(ε * h n)) := by
            have : 0 ≤ 1 + s n := by linarith [hs0 n]
            positivity
          nlinarith [le_abs_self C]
      _ ≤ |C| * t n * (1 + |A| * n) ^ d * Real.exp (-(ε * B * n)) := by
          have : 0 ≤ 1 + s n := by linarith [hs0 n]
          gcongr
      _ = |C| * t n * ((1 + |A| * n) ^ d * Real.exp (-(ε * B * n))) := by ring
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htn]
  calc (t n)⁻¹ * ‖∫ ω, w ω * F n ω ∂μ‖ ≤ (t n)⁻¹ * ((∫ ω, ‖w ω‖ ∂μ) * K) :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.2 htn.le)
    _ ≤ (t n)⁻¹ * ((∫ ω, ‖w ω‖ ∂μ) *
          (|C| * t n * ((1 + |A| * n) ^ d * Real.exp (-(ε * B * n))))) := by
        gcongr
    _ = |C| * (∫ ω, ‖w ω‖ ∂μ) * ((1 + |A| * n) ^ d * Real.exp (-(ε * B * n))) := by
        field_simp
    _ = |C| * (∫ ω, ‖w ω‖ ∂μ) * ((1 + |A| * n) ^ d * Real.exp (-((ε * B) * n))) := by
        ring_nf

end Limit

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The bound (4) of the proof of Proposition VI.4.1 and the vanishing `X⁺ = 0`, from local
bases. `X` is a compact parameter space (the orbit `O`) with a measure and an integrable weight
`w` (the density `μ(ω)`), `E` is a finite-dimensional inner product space (the space
`L(ω, P)^{H×H}` in the compact picture), `ℓ n ω` are linear forms on `E` (in the source
`v ↦ (E^G_P v_ω)^+_{P̄'}(a^{-n})`) and `ψ n ω ∈ E` (the vectors `ψ_{n,ω}`). Near every point
`ω₀` there is a family `b` continuous at `ω₀` and a basis at `ω₀` (the regular rational sections
`ψ'` of `F`) on which the `ℓ n ω` decay like `e^{-ε h(n)}` (from Lemma VI.2.3) and whose inner
products with `ψ n ω` are bounded by `C₄ t(n) (1 + s(n))^d` (from Lemma VI.2.2 and Lemma II.1.1).
With `s(n) ≤ A n` and `h(n) ≥ B n`, `B > 0`, the normalized integrals
`t(n)⁻¹ ∫ w(ω) ℓ n ω (ψ n ω) dω` tend to `0`. -/
theorem tendsto_inv_smul_integral_of_local_basis {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [MeasurableSpace X] (μ : Measure X) {w : X → ℂ} (hw : Integrable w μ)
    (ℓ : ℕ → X → E →ₗ[ℂ] ℂ) (ψ : ℕ → X → E) (t s h : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (hs0 : ∀ n, 0 ≤ s n) {A B : ℝ} (hB : 0 < B) (hs : ∀ n, s n ≤ A * n)
    (hh : ∀ n, B * n ≤ h n)
    (hloc : ∀ ω₀ : X, ∃ k : ℕ, ∃ b : X → Fin k → E, ContinuousAt b ω₀ ∧
      LinearIndependent ℂ (b ω₀) ∧ Submodule.span ℂ (Set.range (b ω₀)) = ⊤ ∧
      ∃ V ∈ 𝓝 ω₀, ∃ ε > 0, ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∃ C₄ : ℝ, ∃ d : ℕ,
        (∀ ω ∈ V, ∀ n i, ‖ℓ n ω (b ω i)‖ ≤ C₂ * Real.exp (-(ε * h n))) ∧
        (∀ ω ∈ V, ∀ n j, ‖inner ℂ (b ω j) (ψ n ω)‖ ≤ C₄ * t n * (1 + s n) ^ d)) :
    Tendsto (fun n => (t n)⁻¹ • ∫ ω, w ω * ℓ n ω (ψ n ω) ∂μ) atTop (𝓝 0) := by
  have hh0 : ∀ n, 0 ≤ h n := fun n => (mul_nonneg hB.le (Nat.cast_nonneg n)).trans (hh n)
  obtain ⟨ε, hε, C, d, hb⟩ := isDecayBoundedOn_of_isCompact isCompact_univ
    (fun n ω => ‖ℓ n ω (ψ n ω)‖) t s h (fun n => (ht n).le) hs0 hh0 (by
      intro ω₀ _
      obtain ⟨k, b, hb, hli, hspan, V, hV, ε, hε, C₂, hC₂, C₄, d, h₂, h₄⟩ := hloc ω₀
      obtain ⟨U, hU, C, hC⟩ := exists_local_decay_of_basis hb hli hspan ℓ ψ t s h hV hC₂ h₂ h₄
      exact ⟨U, hU, ε, hε, C, d, hC⟩)
  exact tendsto_inv_smul_integral_of_decay μ hw (fun n ω => ℓ n ω (ψ n ω)) t s h ht hs0 hB hε
    hs hh fun n => Eventually.of_forall fun ω => hb ω (Set.mem_univ ω) n

end Assembly

end Langlands.HarishChandraSchwartz
