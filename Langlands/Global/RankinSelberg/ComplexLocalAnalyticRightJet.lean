import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! # Analytic uniqueness from complex general linear right derivatives -/

noncomputable section

open Langlands.Archimedean Set Filter Topology
open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

variable {n : ℕ}

local notation "M" => Matrix (Fin n) (Fin n) ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "I" => matrixModel ℂ n

private abbrev unitDomain : Set M := {y | IsUnit y}

local notation "S" => unitDomain (n := n)

private theorem iteratedFDeriv_clm_eq_zero {x : M} (hx : x ∈ S)
    {c : M → M →L[ℝ] ℂ} (hc : ContDiffOn ℝ ∞ c S)
    (j : ℕ) (hz : ∀ v : M, iteratedFDeriv ℝ j (fun y => c y v) x = 0) :
    iteratedFDeriv ℝ j c x = 0 := by
  ext w v
  have hS : IsOpen S := isOpen_setOf_isUnit_matrix
  have he := iteratedFDerivWithin_clm_apply_const_apply hS.uniqueDiffOn hc
    (show (j : ℕ∞ω) ≤ ∞ by simp) hx (u := v) (m := w)
  rw [iteratedFDerivWithin_of_isOpen j hS hx, iteratedFDerivWithin_of_isOpen j hS hx] at he
  rw [← he, hz v]
  rfl

private theorem iteratedFDeriv_comp_eq_zero {x : M} (hx : x ∈ S)
    {c : M → M →L[ℝ] ℂ} {t : M → M →L[ℝ] M}
    (hc : ContDiffOn ℝ ∞ c S) (ht : ContDiffOn ℝ ∞ t S)
    (j : ℕ) (hz : ∀ k ≤ j, iteratedFDeriv ℝ k c x = 0) :
    iteratedFDeriv ℝ j (fun y => (c y).comp (t y)) x = 0 := by
  have hS : IsOpen S := isOpen_setOf_isUnit_matrix
  have hb := (ContinuousLinearMap.compL ℝ M M ℂ).norm_iteratedFDerivWithin_le_of_bilinear
    hc ht hS.uniqueDiffOn hx (show (j : ℕ∞ω) ≤ ∞ by simp)
  rw [iteratedFDerivWithin_of_isOpen j hS hx] at hb
  have hs : (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) *
      ‖iteratedFDerivWithin ℝ k c S x‖ *
      ‖iteratedFDerivWithin ℝ (j - k) t S x‖) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [iteratedFDerivWithin_of_isOpen k hS hx,
      hz k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)), norm_zero, mul_zero, zero_mul]
  rw [hs, mul_zero] at hb
  exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))

/-- If a family of smooth functions is preserved by right differentiation and
all its values vanish at a unit, their entire real matrix jets vanish there. -/
theorem complexLocal_matrixZeroJet_of_rightDerivative {V : Type*}
    (A : V → G → ℂ) (D : M → V → V) (g : G)
    (hSm : ∀ f, ContMDiff I 𝓘(ℝ, ℂ) ∞ (A f))
    (hD : ∀ Y f, rightDerivative I Y (A f) = A (D Y f))
    (h0 : ∀ f, A f g = 0) :
    ∀ j f, iteratedFDeriv ℝ j (unitsExtension (A f)) g.val = 0 := by
  let x : M := g.val
  have hS : IsOpen S := isOpen_setOf_isUnit_matrix
  have hx : x ∈ S := g.isUnit
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro f
    cases j with
    | zero =>
      ext v
      simp only [iteratedFDeriv_zero_apply, zero_apply, unitsExtension_val, h0]
    | succ j =>
      let F := unitsExtension (A f)
      let L := ContinuousLinearMap.mul ℝ M
      let C (y : M) := (fderiv ℝ F y).comp (L y)
      let T (y : M) := L (Ring.inverse y)
      have hF : ContDiffOn ℝ ∞ F S := contDiffOn_unitsExtension (hSm f)
      have hC : ContDiffOn ℝ ∞ C S :=
        (hF.fderiv_of_isOpen hS (by simp)).clm_comp L.contDiff.contDiffOn
      have hT : ContDiffOn ℝ ∞ T S := by
        rintro y ⟨u, rfl⟩
        exact (L.contDiff.contDiffAt.comp _ (contDiffAt_ringInverse ℝ u)).contDiffWithinAt
      have hC0 : ∀ k ≤ j, iteratedFDeriv ℝ k C x = 0 := by
        intro k hk
        apply iteratedFDeriv_clm_eq_zero hx hC k
        intro Y
        have hEq : (fun y => C y Y) =ᶠ[𝓝 x] unitsExtension (A (D Y f)) := by
          filter_upwards [hS.mem_nhds hx] with y hy
          obtain ⟨u, rfl⟩ := hy
          change fderiv ℝ (unitsExtension (A f)) u.val (u.val * Y) =
            unitsExtension (A (D Y f)) u.val
          rw [← rightDerivative_eq_fderiv (hSm f), hD, unitsExtension_val]
        rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
        exact ih k (Nat.lt_succ_of_le hk) _
      have hEq : (fun y => (C y).comp (T y)) =ᶠ[𝓝 x] fderiv ℝ F := by
        filter_upwards [hS.mem_nhds hx] with y hy
        obtain ⟨u, rfl⟩ := hy
        ext Y
        change fderiv ℝ F u.val (u.val * (Ring.inverse u.val * Y)) = _
        rw [Ring.inverse_unit, Units.mul_inv_cancel_left]
      have hfd : iteratedFDeriv ℝ j (fderiv ℝ F) x = 0 := by
        rw [← (hEq.iteratedFDeriv ℝ j).eq_of_nhds]
        exact iteratedFDeriv_comp_eq_zero hx hC hT j hC0
      change iteratedFDeriv ℝ (j + 1) F x = 0
      ext v
      rw [iteratedFDeriv_succ_apply_right, hfd]
      rfl

variable (n) in
/-- An analytic family stable under real right differentiation is zero on
the invertible matrices if all its members vanish at a single unit and the
unit domain is preconnected. -/
def ComplexLocalAnalyticRightJetStatement : Prop :=
  IsPreconnected S →
  ∀ (V : Type) (A : V → G → ℂ) (D : M → V → V) (g : G),
    (∀ f, ContMDiff I 𝓘(ℝ, ℂ) ∞ (A f)) →
    (∀ f, AnalyticOnNhd ℝ (unitsExtension (A f)) S) →
    (∀ Y f, rightDerivative I Y (A f) = A (D Y f)) →
    (∀ f, A f g = 0) →
    ∀ f z, A f z = 0

theorem complexLocalAnalyticRightJet : ComplexLocalAnalyticRightJetStatement n := by
  intro hConn V A D g hSm hAn hD h0 f z
  have hJet := complexLocal_matrixZeroJet_of_rightDerivative A D g hSm hD h0
  obtain ⟨p, r, hp⟩ := hAn f g.val g.isUnit
  have hLocal : unitsExtension (A f) =ᶠ[𝓝 g.val] 0 := by
    filter_upwards [Metric.eball_mem_nhds g.val hp.r_pos] with y hy
    have hy' : y - g.val ∈ Metric.eball 0 r := by simpa [edist_eq_enorm_sub] using hy
    have hsum : HasSum (fun _ : ℕ => (0 : ℂ)) (unitsExtension (A f) y) := by
      simpa only [hJet, zero_apply, smul_zero, add_sub_cancel] using hp.hasSum_iteratedFDeriv hy'
    exact hsum.unique hasSum_zero
  have heq := (hAn f).eqOn_zero_of_preconnected_of_eventuallyEq_zero hConn g.isUnit hLocal
  simpa only [unitsExtension_val, Pi.zero_apply] using heq (Units.isUnit z)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
