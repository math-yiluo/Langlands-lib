import Langlands.Global.RankinSelberg.ComplexLocalDualWhittakerGauge
import Langlands.Global.RankinSelberg.ComplexGodementWhittakerFamily

/-! # Compact parameter bounds for complex Whittaker families and their duals -/

noncomputable section

open Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open Langlands.Archimedean (unitaryCompact)
open Langlands.GeneralLinear (inverseTranspose weylLong upperUnipotent)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexLocalDualWhittakerGauge (weylLong_mem_unitary inverseTranspose_mem_unitary)
open ComplexLocalIwasawa (alpha kpart npart npart_mul_logTorus_mul_kpart alpha_iwasawa)
open ComplexLocalWhittakerGauge (logTorus logTorus_val logTorus_inv_val)
open RealEqualDualConvergence (revNeg rootPos_revNeg sum_abs_revNeg)
open RealConvergenceAnalysis (rootPos)

variable {r : ℕ}
local notation "n" => r + 1
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "U" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "w" => weylLong n ℂ

private theorem inverseTranspose_logTorus' (y : Fin n → ℝ) :
    inverseTranspose n ℂ (logTorus y) = logTorus (-y) := by
  apply Units.ext
  rw [Langlands.GeneralLinear.inverseTranspose_coe, logTorus_inv_val,
    Matrix.diagonal_transpose, logTorus_val]
  rfl

private theorem weylLong_logTorus_revNeg (y : Fin n → ℝ) :
    w * logTorus (-y) * w = logTorus (revNeg y) := by
  apply Units.ext
  ext i j
  rw [Langlands.GeneralLinear.weylLong_conjugate_entry]
  simp only [logTorus_val, Matrix.diagonal_apply, Fin.rev_inj]
  rfl

private theorem weylInverseTranspose_mem_unipotent (u : U) :
    w * inverseTranspose n ℂ u.val * w ∈ U := by
  have he (i j : Fin n) :
      (w * inverseTranspose n ℂ u.val * w).val i j = u⁻¹.val.val j.rev i.rev := by
    rw [Langlands.GeneralLinear.weylLong_conjugate_entry, Langlands.GeneralLinear.inverseTranspose_coe]
    rfl
  refine ⟨fun {i j} hij => ?_, fun i => ?_⟩
  · rw [he]
    exact Langlands.GeneralLinear.UpperUnipotent.entry_eq_zero u⁻¹ (Fin.rev_lt_rev.mpr hij)
  · rw [he]
    exact Langlands.GeneralLinear.UpperUnipotent.entry_diag u⁻¹ i.rev

/-- The Weyl inverse-transpose argument reverses and negates the Iwasawa logarithms. -/
theorem alpha_dualArgument (g : G) : alpha (w * inverseTranspose n ℂ g) = revNeg (alpha g) := by
  let y := alpha g
  let u := npart g
  let k := kpart g
  let U' : U := ⟨w * inverseTranspose n ℂ u.val * w, weylInverseTranspose_mem_unipotent u⟩
  let K' : K := ⟨w * inverseTranspose n ℂ k.val,
    mul_mem (weylLong_mem_unitary n) (inverseTranspose_mem_unitary k)⟩
  have he : w * inverseTranspose n ℂ g = U'.val * logTorus (revNeg y) * K'.val := by
    have hg : u.val * logTorus y * k.val = g := npart_mul_logTorus_mul_kpart g
    conv_lhs => rw [← hg, map_mul, map_mul, inverseTranspose_logTorus']
    calc
      _ = (w * inverseTranspose n ℂ u.val * w⁻¹) * (w * logTorus (-y) * w⁻¹) *
          (w * inverseTranspose n ℂ k.val) := by group
      _ = _ := by rw [Langlands.GeneralLinear.weylLong_inv, weylLong_logTorus_revNeg]
  rw [he, alpha_iwasawa]

/-- Taking a Weyl inverse-transpose dual preserves each uniform simple-root estimate. -/
theorem uniformSimpleRootBound_dual {P : Type*} {S : Set P} {W : P → G → ℂ}
    (hW : HasUniformSimpleRootBound S W) :
    HasUniformSimpleRootBound S (fun p => ArchimedeanLocal.dualFunction n (W p)) := by
  obtain ⟨N, hN⟩ := hW
  refine ⟨N, fun J => ?_⟩
  obtain ⟨C, hC, hb⟩ := hN J
  refine ⟨C, hC, fun q hq g => ?_⟩
  simpa only [ArchimedeanLocal.dualFunction, alpha_dualArgument, sum_abs_revNeg, rootPos_revNeg] using
    hb q hq (w * inverseTranspose n ℂ g)

/-- Local uniform simple-root bounds give a uniform bound on each compact parameter set. -/
theorem uniformSimpleRootBound_compact {P : Type*} [PseudoMetricSpace P] {S : Set P}
    (hS : IsCompact S) (W : P → G → ℂ)
    (hW : ∀ p, ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (Metric.ball p δ) W) :
    HasUniformSimpleRootBound S W := by
  classical
  choose δ hδ hb using hW
  obtain ⟨T, hT⟩ := hS.elim_finite_subcover (fun p => Metric.ball p (δ p)) (fun _ => Metric.isOpen_ball)
    (by intro p _; exact mem_iUnion.mpr ⟨p, Metric.mem_ball_self (hδ p)⟩)
  choose N hN using hb
  let M := T.sup N
  refine ⟨M, fun J => ?_⟩
  choose C hC hCbound using fun p => hN p J
  let D := ∑ p ∈ T, C p
  refine ⟨D, Finset.sum_nonneg fun p _ => hC p, fun q hq g => ?_⟩
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hT hq)
  obtain ⟨hpT, hqp⟩ := mem_iUnion.mp hp
  have hNM : (N p : ℝ) ≤ M := by exact_mod_cast Finset.le_sup hpT
  have hCD : C p ≤ D := Finset.single_le_sum (fun p _ => hC p) hpT
  calc
    _ ≤ C p * Real.exp ((N p : ℝ) * (∑ i, |alpha g i|) - (J : ℝ) * rootPos (alpha g)) :=
      hCbound p q hqp g
    _ ≤ _ := mul_le_mul hCD (Real.exp_le_exp.mpr (sub_le_sub_right
      (mul_le_mul_of_nonneg_right hNM (Finset.sum_nonneg fun i _ => abs_nonneg (alpha g i))) _))
      (Real.exp_nonneg _) (Finset.sum_nonneg fun p _ => hC p)

/-- Locally uniform simple-root estimates give a common compact parameter estimate on the
original family and a compact parameter estimate on the Weyl inverse-transpose dual family. -/
def ComplexLocalUniformDualBoundsStatement : Prop :=
  ∀ {P : Type} [PseudoMetricSpace P] (S : Set P) (W : P → G → ℂ), IsCompact S →
    (∀ p, ∃ δ : ℝ, 0 < δ ∧ HasUniformSimpleRootBound (Metric.ball p δ) W) →
    HasUniformSimpleRootBound S W ∧ HasUniformSimpleRootBound S (fun p => ArchimedeanLocal.dualFunction n (W p))

theorem complexLocalUniformDualBounds : ComplexLocalUniformDualBoundsStatement (r := r) := by
  intro P hP S W hS hW
  have h := uniformSimpleRootBound_compact hS W hW
  exact ⟨h, uniformSimpleRootBound_dual h⟩

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
