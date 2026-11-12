import Langlands.Automorphic.CuspidalAdmissible.CuspPointwise
import Langlands.Automorphic.CuspidalUnitaryForm

/-!
# Square-mean estimates along one-parameter subgroups

For a function on the adelic group with smooth archimedean slices whose basis derivatives are
continuous functions `dφ_k`, the squared difference `|φ(x exp Y) - φ(x)|²` is bounded by
`(C ‖Y‖)²` times the integral over `t ∈ [0, 1]` of `∑_k |dφ_k(x exp(tY))|²`, with a constant
`C` depending only on the fixed basis of the archimedean Lie algebra.
-/

noncomputable section

universe u

open MeasureTheory NumberField
open scoped Classical Topology ENNReal Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

open ArchimedeanGL

/-- The coordinates in the fixed basis are bounded by the operator norm. -/
theorem exists_lieBasis_coeff_bound : ∃ Cb : ℝ, 0 ≤ Cb ∧
    ∀ Zm : ArchimedeanMatrix K n, ∑ k, |(lieBasis K n).repr Zm k| ≤ Cb * ‖Zm‖ := by
  refine ⟨∑ k, ‖LinearMap.toContinuousLinearMap ((lieBasis K n).coord k)‖,
    Finset.sum_nonneg fun _ _ => norm_nonneg _, fun Zm => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  have := (LinearMap.toContinuousLinearMap ((lieBasis K n).coord k)).le_opNorm Zm
  simpa [Real.norm_eq_abs] using this

/-- **Square-mean estimate along a one-parameter subgroup.** -/
theorem exists_exp_pointwise : ∃ Cb : ℝ, 0 ≤ Cb ∧
    ∀ (φ : AdelicGL K n → ℂ)
      (dφ : Fin (Module.finrank ℝ (ArchimedeanMatrix K n)) → AdelicGL K n → ℂ),
      (∀ k, Continuous (dφ k)) →
      (∀ y : FiniteAdelicGL K n, ∃ s : SmoothFunctions K n,
        (∀ g, s.val g = φ (AdelicGL.ofInfinite K n g * AdelicGL.ofFinite K n y)) ∧
        ∀ k g, (smoothDifferential K n (lieDirection K n k) s).val g =
          dφ k (AdelicGL.ofInfinite K n g * AdelicGL.ofFinite K n y)) →
      ∀ (x : AdelicGL K n) (Y : RealLieAlgebra K n),
        ‖φ (x * AdelicGL.ofInfinite K n (infiniteOneParameter K n Y 1)) - φ x‖ₑ ^ 2 ≤
          ENNReal.ofReal ((Cb * ‖realLieAlgebraToMatrix K n Y‖) ^ 2) *
            ∫⁻ t in Set.Icc (0 : ℝ) 1, ∑ k, ‖dφ k
              (x * AdelicGL.ofInfinite K n (infiniteOneParameter K n Y t))‖ₑ ^ 2 := by
  obtain ⟨Cb, hCb, hbound⟩ := exists_lieBasis_coeff_bound K n
  refine ⟨Cb, hCb, fun φ dφ hdφ hslice x Y => ?_⟩
  obtain ⟨s, hs, hsd⟩ := hslice (AdelicGL.finite K n x)
  set a := AdelicGL.infinite K n x with ha
  set c := infiniteOneParameter K n Y with hc
  have hpt : ∀ t, x * AdelicGL.ofInfinite K n (c t) =
      AdelicGL.ofInfinite K n (a * c t) * AdelicGL.ofFinite K n (AdelicGL.finite K n x) := by
    intro t
    refine AdelicGL.ext_infinite_finite K n ?_ ?_ <;> simp [ha]
  set coef : Fin (Module.finrank ℝ (ArchimedeanMatrix K n)) → ℝ :=
    fun k => (lieBasis K n).repr (realLieAlgebraToMatrix K n Y) k with hcoef
  set D : ℝ → ℂ := fun t => ∑ k, (coef k : ℂ) * dφ k (x * AdelicGL.ofInfinite K n (c t))
    with hD
  have hDc : Continuous D :=
    continuous_finsetSum _ fun k _ => continuous_const.mul ((hdφ k).comp
      (continuous_const.mul ((map_continuous (AdelicGL.ofInfinite K n)).comp
        (continuous_infiniteOneParameter K n Y))))
  have hderiv : ∀ t, HasDerivAt (fun u => s.val (a * c u)) (D t) t := by
    intro t
    have h := hasDerivAt_smooth_oneParameter K n s Y a t
    refine h.congr_deriv ?_
    have hsum := smoothDifferential_val_eq_sum s (realLieAlgebraToMatrix K n Y) (a * c t)
    rw [LinearEquiv.symm_apply_apply] at hsum
    rw [hsum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsd k, ← hpt]
  have hftc : s.val (a * c 1) - s.val (a * c 0) = ∫ t in (0 : ℝ)..1, D t :=
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hDc.intervalIntegrable 0 1)).symm
  have h1 : s.val (a * c 1) = φ (x * AdelicGL.ofInfinite K n (c 1)) := by
    rw [hs, hpt]
  have h0 : s.val (a * c 0) = φ x := by
    rw [hc, infiniteOneParameter_zero, mul_one, hs, ha]
    exact congrArg φ (AdelicGL.eq_ofInfinite_mul_ofFinite K n x).symm
  rw [← h1, ← h0, hftc, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have hcoefb : ∑ k, |coef k| ≤ Cb * ‖realLieAlgebraToMatrix K n Y‖ := hbound _
  calc ‖∫ t in Set.Icc (0 : ℝ) 1, D t‖ₑ ^ 2
      ≤ (∫⁻ t in Set.Icc (0 : ℝ) 1, ‖D t‖ₑ) ^ 2 := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ‖D t‖ₑ ^ 2 :=
        Langlands.Automorphic.CuspidalAdmissible.sq_lintegral_le _ hDc.enorm.aemeasurable
    _ ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal ((Cb * ‖realLieAlgebraToMatrix K n Y‖) ^ 2) *
          ∑ k, ‖dφ k (x * AdelicGL.ofInfinite K n (c t))‖ₑ ^ 2 := by
        refine lintegral_mono fun t => ?_
        refine (Langlands.Automorphic.CuspidalAdmissible.enorm_sum_mul_sq_le Finset.univ coef
          _).trans ?_
        gcongr
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end Langlands.Global
