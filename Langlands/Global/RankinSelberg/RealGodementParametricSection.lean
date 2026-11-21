import Langlands.Analysis.SeveralComplex.ParametricIntegral
import Langlands.Global.RankinSelberg.RealGodementColumnParameter

/-! # Godement sections with holomorphically varying real principal-series data -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SeveralComplex
open MeasureTheory Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealJacquetFrobenius

variable {m n : ℕ}

local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "P" => (Fin n → ℂ)

/-- A variable exponent gives a continuous family of determinant weights. -/
theorem continuous_determinantWeight_family {r : ℕ} (p : Fin 2) (v : ℂ)
    {s : P → ℂ} (hs : Continuous s) :
    Continuous (fun q : P × Langlands.GeneralLinear r ℝ => determinantWeight (charData p (s q.1)) v q.2) := by
  have hLog : Continuous (fun h : Langlands.GeneralLinear r ℝ => Real.log |h.val.det|) :=
    Units.continuous_val.matrix_det.abs.log (fun h => abs_ne_zero.mpr (determinant h).ne_zero)
  simp_rw [determinantWeight_exponent_shift p v (s _) 0 _, sub_zero]
  exact ((contMDiff_determinantWeight (charData p 0) v).continuous.comp continuous_snd).mul
    (((hs.comp continuous_fst).mul ((Complex.continuous_ofReal.comp hLog).comp continuous_snd)).cexp)

/-- A compact full-row-rank Godement test gives a holomorphic upper section when the
lower section and leading exponent vary holomorphically. -/
def RealGodementParametricSectionStatement : Prop :=
  ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (p : Fin 2) (s : P → ℂ), Differentiable ℂ s →
    ∀ (f : P → G → ℂ), Continuous (fun q : P × G => f q.1 q.2) →
      (∀ h, Differentiable ℂ (fun z => f z h)) →
    ∀ (S : Set X), IsCompact S → (∀ x ∈ S, HasFullRowRank x) →
    ∀ (Φ : X → ℂ), Continuous Φ → (∀ x ∉ S, Φ x = 0) →
    ∀ g : H, Differentiable ℂ (fun z => sectionValue μ (charData p (s z)) (f z) Φ g)

theorem realGodementParametricSection : RealGodementParametricSectionStatement (m := m) (n := n) := by
  intro _ _ μ _ p s hs f hf hd S hS hR Φ hΦ hZero g
  let v : ℂ := (((m : ℂ) + 1) / 2)
  let v' : ℂ := (m : ℂ) / 2
  let F (z : P) (h : G) := f z h⁻¹ * determinantWeight (charData p (s z)) v h * Φ (rowPoint h.val g)
  let V := {h : G | ∃ k ∈ ({g} : Set H), rowPoint h.val k ∈ S}
  have hV : IsCompact V := isCompact_support_preimage isCompact_singleton hS hR
  let : IsFiniteMeasure (μ.restrict V) := isFiniteMeasure_restrict.mpr hV.measure_lt_top.ne
  have hFZero (z : P) (h : G) (hh : h ∉ V) : F z h = 0 := by
    unfold F
    rw [hZero _ (fun hx => hh ⟨g, mem_singleton g, hx⟩), mul_zero]
  have hF (h : G) : Differentiable ℂ (fun z => F z h) := by
    have hDet : Differentiable ℂ (fun z => determinantWeight (charData p (s z)) v h) := by
      simp_rw [determinantWeight_exponent_shift p v (s _) 0 h, sub_zero]
      exact ((hs.mul_const _).cexp).const_mul _
    exact ((hd h⁻¹).mul hDet).mul_const _
  have hJoint : Continuous (fun q : P × G => F q.1 q.2) := by
    have hRow : Continuous (fun h : G => rowPoint h.val g) :=
      Units.continuous_val.matrix_mul continuous_const
    have hInv : Continuous (fun q : P × G => (q.1, q.2⁻¹)) :=
      continuous_fst.prodMk continuous_snd.inv
    exact ((hf.comp hInv).mul (continuous_determinantWeight_family p v hs.continuous)).mul
      (hΦ.comp (hRow.comp continuous_snd))
  have hI : Differentiable ℂ (fun z => ∫ h in V, F z h ∂μ) := by
    apply differentiableOn_univ.mp
    refine differentiableOn_integral_of_bounded (μ.restrict V) F isOpen_univ
      (fun h => (hF h).differentiableOn) ?_ ?_
    · intro z _
      exact (hJoint.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    · intro K _ hK
      obtain ⟨B, hB⟩ := (hK.prod hV).exists_bound_of_continuousOn hJoint.continuousOn
      refine ⟨max B 0, fun z hz h => ?_⟩
      by_cases hh : h ∈ V
      · exact (hB (z, h) ⟨hz, hh⟩).trans (le_max_left B 0)
      · rw [hFZero z h hh, norm_zero]
        exact le_max_right B 0
  have hOuter : Differentiable ℂ (fun z => determinantWeight (charData p (s z)) v' g) := by
    simp_rw [determinantWeight_exponent_shift p v' (s _) 0 g, sub_zero]
    exact ((hs.mul_const _).cexp).const_mul _
  have hEq (z : P) : sectionValue μ (charData p (s z)) (f z) Φ g =
      determinantWeight (charData p (s z)) v' g * ∫ h in V, F z h ∂μ := by
    change _ * (∫ h, F z h ∂μ) = _
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (hFZero z)]
  simp_rw [hEq]
  exact hOuter.mul hI

end Langlands.Global.RankinSelbergGlobal.RealGodement
