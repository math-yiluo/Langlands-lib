import Langlands.Global.RankinSelberg.RealGodementSection
import Langlands.Global.RankinSelberg.RealConvergenceAnalysis
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # The real Godement section is entire in its leading exponent -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open MeasureTheory Matrix Set
open scoped ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealConvergenceAnalysis RealJacquetFrobenius

private def logAbsDet {m : ℕ} (h : Langlands.GeneralLinear m ℝ) : ℝ := Real.log |h.val.det|

private theorem continuous_logAbsDet_section {m : ℕ} :
    Continuous (logAbsDet (m := m)) :=
  Units.continuous_val.matrix_det.abs.log (fun h => abs_ne_zero.mpr (determinant h).ne_zero)

private theorem determinantWeight_charData_factor {m : ℕ} (p : Fin 2) (s z : ℂ)
    (h : Langlands.GeneralLinear m ℝ) :
    determinantWeight (charData p z) s h =
      determinantWeight (charData p 0) s h * Complex.exp (z * (logAbsDet h : ℂ)) := by
  let d := determinant h
  let b : ℂ := (|(d : ℝ)| : ℝ)
  change ((charData p z).character d : ℂ) * b ^ s =
    ((charData p 0).character d : ℂ) * b ^ s * Complex.exp (z * (logAbsDet h : ℂ))
  rw [(charData p z).character_eq, (charData p 0).character_eq]
  simp only [charData, Complex.cpow_zero, mul_one]
  have hb : b ≠ 0 := by
    change ((|(d : ℝ)| : ℝ) : ℂ) ≠ 0
    exact_mod_cast abs_ne_zero.mpr d.ne_zero
  rw [Complex.cpow_def_of_ne_zero hb]
  have hLog : Complex.log b = (logAbsDet h : ℂ) :=
    (Complex.ofReal_log (abs_nonneg (d : ℝ))).symm
  rw [hLog, mul_comm z (logAbsDet h : ℂ)]
  ring

private theorem continuous_determinantWeight_charData_zero {m : ℕ} (p : Fin 2) (s : ℂ) :
    Continuous (determinantWeight (n := m) (charData p 0) s : Langlands.GeneralLinear m ℝ → ℂ) := by
  have hd : Continuous (fun h : Langlands.GeneralLinear m ℝ => h.val.det) := Units.continuous_val.matrix_det
  have hc : Continuous (fun h : Langlands.GeneralLinear m ℝ => charFun p 0 h.val.det) := by
    apply continuous_iff_continuousAt.mpr
    intro h
    have hc : ContinuousAt (charFun p 0) h.val.det :=
      (contDiffAt_charFun p 0 (determinant h).ne_zero).continuousAt
    exact ContinuousAt.comp (f := fun k : Langlands.GeneralLinear m ℝ => k.val.det)
      hc (hd.continuousAt (x := h))
  have hexp : Continuous (fun h : Langlands.GeneralLinear m ℝ => Complex.exp (s * (logAbsDet h : ℂ))) :=
    ((Complex.continuous_ofReal.comp continuous_logAbsDet_section).const_mul s).cexp
  have h (h : Langlands.GeneralLinear m ℝ) : determinantWeight (charData p 0) s h =
      charFun p 0 h.val.det * Complex.exp (s * (logAbsDet h : ℂ)) := by
    change charFun p 0 h.val.det * ((|h.val.det| : ℝ) : ℂ) ^ s = _
    have hb : ((|h.val.det| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr (determinant h).ne_zero
    rw [Complex.cpow_def_of_ne_zero hb, ← Complex.ofReal_log (abs_nonneg _), logAbsDet, mul_comm s]
  rw [funext h]
  exact hc.mul hexp

/-- Each value of a compact full-row-rank Godement section is entire as the
leading exponent varies with fixed parity. -/
def RealGodementSectionAnalyticStatement : Prop :=
  ∀ (m : ℕ) [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)] (μ : Measure (Langlands.GeneralLinear m ℝ))
    [IsFiniteMeasureOnCompacts μ] (p : Fin 2)
    (f : Langlands.GeneralLinear m ℝ → ℂ), Continuous f →
    ∀ (S : Set (Matrix (Fin m) (Fin (m + 1)) ℝ)), IsCompact S →
      (∀ x ∈ S, HasFullRowRank x) →
    ∀ (Φ : Matrix (Fin m) (Fin (m + 1)) ℝ → ℂ), Continuous Φ → (∀ x ∉ S, Φ x = 0) →
    ∀ g : Langlands.GeneralLinear (m + 1) ℝ,
      Differentiable ℂ (fun z : ℂ => sectionValue μ (charData p z) f Φ g)

theorem realGodementSectionAnalytic : RealGodementSectionAnalyticStatement := by
  intro m _ _ μ _ p f hf S hS hRank Φ hΦ hΦS g
  let G := Langlands.GeneralLinear m ℝ
  let s := ((m : ℂ) + 1) / 2
  let s' := (m : ℂ) / 2
  let B := fun h : G => f h⁻¹ * determinantWeight (charData p 0) s h * Φ (rowPoint h.val g)
  have hRow : Continuous (fun h : G => rowPoint h.val g) := Units.continuous_val.matrix_mul continuous_const
  have hB : Continuous B :=
    ((hf.comp continuous_inv).mul (continuous_determinantWeight_charData_zero p s)).mul (hΦ.comp hRow)
  let V := {h : G | ∃ k ∈ ({g} : Set (Langlands.GeneralLinear (m + 1) ℝ)), rowPoint h.val k ∈ S}
  have hV : IsCompact V := isCompact_support_preimage isCompact_singleton hS hRank
  have hSupport : Function.support B ⊆ V := by
    intro h hh
    by_contra hn
    have hz := hΦS (rowPoint h.val g) (fun hx => hn ⟨g, mem_singleton _, hx⟩)
    exact hh (by simp only [B, hz, mul_zero])
  have hSupportNorm : HasCompactSupport (fun h : G => ‖B h‖) := by
    refine hV.of_isClosed_subset isClosed_closure (closure_minimal ?_ hV.isClosed)
    intro h hh
    apply hSupport
    simpa only [Function.mem_support, norm_ne_zero_iff] using hh
  have hInt (β : ℝ) : Integrable (fun h : G => ‖B h‖ * Real.exp (β * logAbsDet h)) μ :=
    Continuous.integrable_of_hasCompactSupport
      (hB.norm.mul (Real.continuous_exp.comp (continuous_logAbsDet_section.const_mul β)))
      hSupportNorm.mul_right
  have hInner : Differentiable ℂ (fun z : ℂ => ∫ h : G, B h * Complex.exp (z * (logAbsDet h : ℂ)) ∂μ) := by
    intro z
    have h := differentiableOn_integral_cexp_mul (σ := z.re - 1)
      hB.aestronglyMeasurable continuous_logAbsDet_section.aestronglyMeasurable (fun β _ => hInt β)
    exact h.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by
      dsimp
      linarith))
  have hOuter : Differentiable ℂ (fun z : ℂ => determinantWeight (charData p z) s' g) := by
    rw [funext fun z => determinantWeight_charData_factor p s' z g]
    exact ((differentiable_id.mul_const (logAbsDet g : ℂ)).cexp).const_mul _
  have hValue (z : ℂ) : sectionValue μ (charData p z) f Φ g =
      determinantWeight (charData p z) s' g * ∫ h : G, B h * Complex.exp (z * (logAbsDet h : ℂ)) ∂μ := by
    unfold sectionValue innerIntegral
    congr 1
    refine integral_congr_ae (ae_of_all _ fun h => ?_)
    change f h⁻¹ * determinantWeight (charData p z) s h * Φ (rowPoint h.val g) = _
    rw [determinantWeight_charData_factor p s z]
    unfold B
    ring
  rw [funext hValue]
  exact hOuter.mul hInner

end Langlands.Global.RankinSelbergGlobal.RealGodement
