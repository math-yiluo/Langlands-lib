import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Separating a point by smooth bumps pulled back along a proper-over-`U` map

`eq_zero_of_integral_smoothBump_eq_zero`: let `p : H → M` be a continuous map to a
finite-dimensional real normed space, with compact preimages of compact subsets of an open set
`U ∋ p h₀`. Let `F : H → ℂ` be continuous and constant on the fiber of `p` through `h₀`. If
`∫ h, β (p h) * F h ∂μ = 0` for every smooth real bump `β` with compact support inside `U`,
then `F h₀ = 0`. `CompactFiberBumpSeparationStatement` packages this. See the paired Markdown.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff

set_option autoImplicit false

universe u v

namespace Langlands.Analysis

/-- **Bump separation on a compact fiber.** Let `H` be a Hausdorff space with a Borel measure `μ`
that is finite on compact sets and positive on nonempty open sets. Let `p : H → M` be continuous,
`M` a finite-dimensional real normed space, and `U ⊆ M` open with `p h₀ ∈ U` such that `p`
has compact preimages of compact subsets of `U`. If a continuous `F : H → ℂ`, constant on the
fiber `p⁻¹ {p h₀}`, integrates to zero against `β ∘ p` for every smooth real `β` with compact
support inside `U`, then `F h₀ = 0`. -/
def CompactFiberBumpSeparationStatement : Prop :=
  ∀ {H : Type u} [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [OpensMeasurableSpace H]
    (μ : Measure H) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    {M : Type v} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
    (p : H → M) (U : Set M) (h₀ : H) (F : H → ℂ),
    Continuous p → IsOpen U → p h₀ ∈ U →
    (∀ S : Set M, IsCompact S → S ⊆ U → IsCompact (p ⁻¹' S)) →
    Continuous F → (∀ h, p h = p h₀ → F h = F h₀) →
    (∀ β : M → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ U →
      ∫ h, (β (p h) : ℂ) * F h ∂μ = 0) →
    F h₀ = 0

section

variable {H : Type*} [TopologicalSpace H] [T2Space H] [MeasurableSpace H] [OpensMeasurableSpace H]
  (μ : Measure H) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
  {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

theorem eq_zero_of_integral_smoothBump_eq_zero {p : H → M} {U : Set M} {h₀ : H} {F : H → ℂ}
    (hp : Continuous p) (hU : IsOpen U) (hh₀ : p h₀ ∈ U)
    (hproper : ∀ S : Set M, IsCompact S → S ⊆ U → IsCompact (p ⁻¹' S))
    (hF : Continuous F) (hfiber : ∀ h, p h = p h₀ → F h = F h₀)
    (hint : ∀ β : M → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β → tsupport β ⊆ U →
      ∫ h, (β (p h) : ℂ) * F h ∂μ = 0) :
    F h₀ = 0 := by
  by_contra hc
  set c := F h₀ with hc_def
  -- the real part of `conj c * F`, positive near the fiber
  let G : H → ℝ := fun h => (starRingEnd ℂ c * F h).re
  have hG : Continuous G := Complex.continuous_re.comp (continuous_const.mul hF)
  have hGc : G h₀ = Complex.normSq c := by
    change (starRingEnd ℂ c * c).re = _
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re]
  have hpos : 0 < G h₀ := by rw [hGc]; exact Complex.normSq_pos.mpr hc
  have hGfiber : ∀ h, p h = p h₀ → G h = G h₀ := fun h hh => by
    change (starRingEnd ℂ c * F h).re = (starRingEnd ℂ c * F h₀).re
    rw [hfiber h hh]
  -- a closed ball around `p h₀` inside `U`
  obtain ⟨ε₀, hε₀, hball⟩ := Metric.isOpen_iff.mp hU (p h₀) hh₀
  set r := ε₀ / 2 with hr_def
  have hr : 0 < r := half_pos hε₀
  have hrU : closedBall (p h₀) r ⊆ U :=
    (closedBall_subset_ball (half_lt_self hε₀)).trans hball
  -- the compact set of points over the ball where `G` is small
  let A : Set H := p ⁻¹' closedBall (p h₀) r ∩ {h | G h ≤ G h₀ / 2}
  have hA : IsCompact A :=
    (hproper _ (isCompact_closedBall _ _) hrU).inter_right
      (isClosed_le hG continuous_const)
  have hpA : p h₀ ∉ p '' A := by
    rintro ⟨h, ⟨-, hh⟩, hph⟩
    have : G h ≤ G h₀ / 2 := hh
    rw [hGfiber h hph] at this
    linarith
  obtain ⟨ε, hε, hεA⟩ :=
    Metric.isOpen_iff.mp (hA.image hp).isClosed.isOpen_compl (p h₀) hpA
  set ε' := min ε r with hε'_def
  have hε' : 0 < ε' := lt_min hε hr
  -- the bump
  let β : ContDiffBump (p h₀) := ⟨ε' / 2, ε', half_pos hε', half_lt_self hε'⟩
  have hβ_supp : ∀ y, β y ≠ 0 → y ∈ ball (p h₀) ε' := fun y hy => by
    have : y ∈ Function.support β := hy
    rwa [β.support_eq] at this
  have hβU : tsupport β ⊆ U := by
    rw [β.tsupport_eq]
    exact (closedBall_subset_closedBall (min_le_right _ _)).trans hrU
  have hβ1 : β (p h₀) = 1 := β.one_of_mem_closedBall (mem_closedBall_self (half_pos hε').le)
  -- the integrand `β (p h) * G h`
  let f : H → ℝ := fun h => β (p h) * G h
  have hf_cont : Continuous f := (β.continuous.comp hp).mul hG
  have hsupp_sub : ∀ h, β (p h) ≠ 0 → h ∈ p ⁻¹' tsupport β := fun h hh =>
    subset_tsupport _ (Function.mem_support.mpr hh)
  have hK : IsCompact (p ⁻¹' tsupport β) := hproper _ β.hasCompactSupport.isCompact hβU
  have hf_comp : HasCompactSupport f :=
    HasCompactSupport.intro hK fun h hh => by
      have : β (p h) = 0 := by
        by_contra hne
        exact hh (hsupp_sub h hne)
      simp [f, this]
  have hf_nonneg : 0 ≤ f := fun h => by
    by_cases hβh : β (p h) = 0
    · simp [f, hβh]
    · have hmem := hβ_supp _ hβh
      have hGh : G h₀ / 2 < G h := by
        by_contra hle
        rw [not_lt] at hle
        have hAh : h ∈ A :=
          ⟨ball_subset_closedBall ((ball_subset_ball (min_le_right _ _)) hmem), hle⟩
        exact hεA ((ball_subset_ball (min_le_left _ _)) hmem) ⟨h, hAh, rfl⟩
      exact mul_nonneg β.nonneg (by linarith)
  have hf_h₀ : f h₀ ≠ 0 := by
    simp only [f, hβ1, one_mul]
    exact hpos.ne'
  have hf_pos : 0 < ∫ h, f h ∂μ :=
    hf_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hf_comp hf_nonneg hf_h₀
  -- but the integral of `f` is the real part of `conj c` times a vanishing integral
  have hzero := hint (fun y => β y) (β.contDiff (n := ⊤)) β.hasCompactSupport hβU
  let g : H → ℂ := fun h => starRingEnd ℂ c * ((β (p h) : ℂ) * F h)
  have hg_cont : Continuous g :=
    continuous_const.mul ((Complex.continuous_ofReal.comp (β.continuous.comp hp)).mul hF)
  have hg_comp : HasCompactSupport g :=
    HasCompactSupport.intro hK fun h hh => by
      have : β (p h) = 0 := by
        by_contra hne
        exact hh (hsupp_sub h hne)
      simp [g, this]
  have hg_int : Integrable g μ := hg_cont.integrable_of_hasCompactSupport hg_comp
  have hfg : ∀ h, f h = RCLike.re (g h) := fun h => by
    change β (p h) * (starRingEnd ℂ c * F h).re =
      (starRingEnd ℂ c * ((β (p h) : ℂ) * F h)).re
    rw [mul_left_comm, Complex.re_ofReal_mul]
  have : ∫ h, f h ∂μ = 0 := by
    simp_rw [hfg]
    rw [integral_re hg_int, integral_const_mul, hzero, mul_zero, map_zero]
  linarith

/-- Proof of `CompactFiberBumpSeparationStatement`. -/
theorem compactFiberBumpSeparation : CompactFiberBumpSeparationStatement.{u, v} := by
  intro H _ _ _ _ μ _ _ M _ _ _ p U h₀ F hp hU hh₀ hproper hF hfiber hint
  exact eq_zero_of_integral_smoothBump_eq_zero μ hp hU hh₀ hproper hF hfiber hint

end

end Langlands.Analysis
