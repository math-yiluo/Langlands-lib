import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellConvergenceStatement
import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellPointwise
import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellContinuity

/-! # Absolute convergence of the open-cell integral: the proof

The open-cell integrand is continuous (`OpenCellContinuity.continuous_openCellIntegrand`). For
`s` with `e = Re s + b ≥ 0` it is bounded by a constant times the majorant `Ω_e(Y)`
(`OpenCellPointwise.exists_norm_openCellIntegrand_le`), whose lower integral is finite once `e`
exceeds both the real dimension `d` of the archimedean coordinates and `D + 1`,
`D = (t + 1)(r + 1)` (`OpenCellMajorant.lintegral_majorant_lt_top`); `σ = max(d, D + 1) - b`.
See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

namespace Langlands.Global

open MeasureTheory NumberField CuspidalPairEisenstein

/-- **Absolute convergence of the open-cell integral.** -/
theorem cuspidalPairEisensteinOpenCellConvergence :
    CuspidalPairEisensteinOpenCellConvergenceStatement.{u} := by
  intro F _ _ _ r t T T' _ _ ψ hψ φ hφ
  obtain ⟨b, hb⟩ := OpenCellPointwise.exists_norm_openCellIntegrand_le ψ hψ hφ
  set d : ℝ := (Module.finrank ℝ
    (RankinSelbergGlobal.EqualAnalytic.ArchRow F ((t + 1) * (r + 1))) : ℝ)
  set D : ℝ := (((t + 1) * (r + 1) : ℕ) : ℝ)
  refine ⟨max d (D + 1) - b, fun s hs => ?_⟩
  let _ : MeasurableSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := borel _
  have : BorelSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) := ⟨rfl⟩
  have : LocallyCompactSpace (Adeles F) := adeles_locallyCompactSpace F
  have : LocallyCompactSpace (Matrix (Fin (t + 1)) (Fin (r + 1)) (Adeles F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (t + 1) → Fin (r + 1) → Adeles F))
  have hμ : (openCellHaar F r t).IsAddHaarMeasure := by
    unfold openCellHaar
    infer_instance
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have he1 : d < s.re + b := by
    have := le_max_left d (D + 1)
    linarith
  have he2 : D + 1 < s.re + b := by
    have := le_max_right d (D + 1)
    linarith
  obtain ⟨C, hC, hbound⟩ := hb s (by linarith)
  refine ⟨(OpenCellContinuity.continuous_openCellIntegrand ψ hψ hφ s).aestronglyMeasurable, ?_⟩
  calc ∫⁻ Y, ‖openCellIntegrand ψ φ s Y‖ₑ ∂(openCellHaar F r t)
      ≤ ∫⁻ Y, ENNReal.ofReal C * ENNReal.ofReal (OpenCellMajorant.majorant (s.re + b) Y)
          ∂(openCellHaar F r t) := by
        refine lintegral_mono fun Y => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hbound Y)
    _ = ENNReal.ofReal C * ∫⁻ Y, ENNReal.ofReal (OpenCellMajorant.majorant (s.re + b) Y)
          ∂(openCellHaar F r t) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (OpenCellMajorant.lintegral_majorant_lt_top (openCellHaar F r t) he1 he2)

end Langlands.Global
