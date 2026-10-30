import Langlands.Analysis.CoordinateScalarLocalEllipticityStatement
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Order.Compact

/-! # Compactness proof of the local uniform symbol bound -/

noncomputable section
universe v
open scoped Topology
set_option autoImplicit false

namespace Langlands.Analysis

variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] {d r : ℕ}

theorem coordinateScalarLocalEllipticity :
    CoordinateScalarLocalEllipticityStatement E d r := by
  classical
  intro hr D x₀ hcoeff hell
  let : FiniteDimensional ℝ E := D.basis.finiteDimensional_of_finite
  have hsymbol : Continuous (fun ξ : E →L[ℝ] ℝ => D.principalSymbol x₀ ξ) := by
    unfold CoordinateScalarOperator.principalSymbol
    apply continuous_finsetSum
    intro w _
    apply continuous_const.mul
    apply continuous_finsetProd
    intro j _
    exact Complex.continuous_ofReal.comp
      (ContinuousLinearMap.apply ℝ ℝ (D.basis (w j))).continuous
  have hjoint (η : E →L[ℝ] ℝ) :
      ContinuousAt
        (fun z : E × (E →L[ℝ] ℝ) => D.principalSymbol z.1 z.2) (x₀, η) := by
    unfold CoordinateScalarOperator.principalSymbol
    apply tendsto_finsetSum
    intro w _
    apply ((hcoeff w).comp continuousAt_fst).mul
    apply tendsto_finsetProd
    intro j _
    exact Complex.continuous_ofReal.continuousAt.comp
      ((ContinuousLinearMap.apply ℝ ℝ (D.basis (w j))).continuous.continuousAt.comp
        continuousAt_snd)
  have hcompact : IsCompact (Metric.sphere (0 : E →L[ℝ] ℝ) 1) :=
    isCompact_sphere _ _
  obtain ⟨b, hb, hmin⟩ := hcompact.exists_forall_le' hsymbol.norm.continuousOn
    (a := (0 : ℝ)) (by
      intro η hη
      apply norm_pos_iff.mpr
      apply hell η
      intro heq
      simp [heq] at hη)
  have hnear :
      ∀ᶠ x in 𝓝 x₀, ∀ η ∈ Metric.sphere (0 : E →L[ℝ] ℝ) 1,
        b / 2 < ‖D.principalSymbol x η‖ := by
    apply hcompact.eventually_forall_of_forall_eventually
    intro η hη
    apply (hjoint η).norm.eventually
    apply lt_mem_nhds
    have := hmin η hη
    linarith
  obtain ⟨U, hU, hUopen, hx₀⟩ := eventually_nhds_iff.mp hnear
  refine ⟨U, hUopen, hx₀, b / 2, half_pos hb, ?_⟩
  intro x hx ξ
  by_cases hξ : ξ = 0
  · subst ξ
    simpa only [norm_zero, zero_pow (Nat.ne_of_gt hr), mul_zero] using
      norm_nonneg (D.principalSymbol x 0)
  have hnorm : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr hξ
  let η : E →L[ℝ] ℝ := ‖ξ‖⁻¹ • ξ
  have hηnorm : ‖η‖ = 1 := by
    dsimp [η]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hnorm]
  have hη : η ∈ Metric.sphere (0 : E →L[ℝ] ℝ) 1 := by
    simpa using hηnorm
  have hscale : ‖ξ‖ • η = ξ := by
    dsimp [η]
    rw [smul_smul, mul_inv_cancel₀ hnorm, one_smul]
  have hsymbolNorm :
      ‖D.principalSymbol x ξ‖ = ‖ξ‖ ^ r * ‖D.principalSymbol x η‖ := by
    calc
      ‖D.principalSymbol x ξ‖ = ‖D.principalSymbol x (‖ξ‖ • η)‖ :=
        congrArg (fun ζ => ‖D.principalSymbol x ζ‖) hscale.symm
      _ = ‖ξ‖ ^ r * ‖D.principalSymbol x η‖ := by
        rw [D.principalSymbol_smul, norm_mul, norm_pow, Complex.norm_real,
          Real.norm_of_nonneg (norm_nonneg ξ)]
  calc
    b / 2 * ‖ξ‖ ^ r = ‖ξ‖ ^ r * (b / 2) := mul_comm _ _
    _ ≤ ‖ξ‖ ^ r * ‖D.principalSymbol x η‖ :=
      mul_le_mul_of_nonneg_left (hU x hx η hη).le (pow_nonneg (norm_nonneg ξ) _)
    _ = ‖D.principalSymbol x ξ‖ := hsymbolNorm.symm

end Langlands.Analysis
