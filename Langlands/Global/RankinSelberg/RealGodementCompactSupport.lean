import Langlands.Representation.RankinSelberg.AdjacentRankCompactOrbit
import Langlands.Global.RankinSelberg.UnequalAnalyticHolomorphy
import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Compact full-row-rank support in the real Godement integral -/

noncomputable section

open MeasureTheory Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "Y" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ

/-- The last `m` rows, used for the upper triangular Borel convention. -/
def lastRows (g : Y) : X := fun i j => g i.succ j

/-- The rectangular matrix `(0, h) g` in the Godement integral. -/
def rowPoint (h : M) (g : H) : X := h * lastRows g.val

/-- Full row rank, expressed by existence of a right inverse. -/
def HasFullRowRank (x : X) : Prop :=
  Langlands.RankinSelberg.AdjacentRankFullRank x

private def recover (g : H) (x : X) : M := fun i j => (x * (g⁻¹).val) i j.succ

private theorem continuous_rowPoint :
    Continuous (fun p : M × H => rowPoint p.1 p.2) := by
  have hv : Continuous (Units.val : H → Y) := Units.continuous_val
  have hr : Continuous (lastRows : Y → X) :=
    continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i.succ)
  exact continuous_fst.matrix_mul (hr.comp (hv.comp continuous_snd))

private theorem continuous_recover :
    Continuous (fun p : H × X => recover p.1 p.2) :=
  continuous_matrix fun i j => (continuous_apply j.succ).comp ((continuous_apply i).comp
    (continuous_snd.matrix_mul (Units.continuous_coe_inv.comp continuous_fst)))

private theorem recover_rowPoint (h : M) (g : H) : recover g (rowPoint h g) = h := by
  have hRows : lastRows g.val * (g⁻¹).val = lastRows (1 : Y) := by
    ext i j
    change (g.val * (g⁻¹).val) i.succ j = (1 : Y) i.succ j
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  ext i j
  change ((h * lastRows g.val) * (g⁻¹).val) i j.succ = h i j
  rw [Matrix.mul_assoc, hRows]
  simp only [Matrix.mul_apply, lastRows, Matrix.one_apply, Fin.succ_inj, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem isUnit_of_hasFullRowRank {h : M} {g : H}
    (hr : HasFullRowRank (rowPoint h g)) : IsUnit h := by
  obtain ⟨b, hb⟩ := hr
  have hRight : h * (lastRows g.val * b) = 1 := by
    rw [← Matrix.mul_assoc]
    exact hb
  exact (Matrix.isUnit_iff_isUnit_det h).mpr (Matrix.isUnit_det_of_right_inverse hRight)

/-- The lower-rank integration variable stays in a compact set, uniformly over a
compact set of translating matrices. -/
theorem isCompact_support_preimage {T : Set H} {S : Set X} (hT : IsCompact T)
    (hS : IsCompact S) (hRank : ∀ x ∈ S, HasFullRowRank x) :
    IsCompact {h : G | ∃ g ∈ T, rowPoint h.val g ∈ S} := by
  let graph : Set (H × X) := {p | rowPoint (recover p.1 p.2) p.1 = p.2}
  have hGraph : IsClosed graph :=
    isClosed_eq (continuous_rowPoint.comp (continuous_recover.prodMk continuous_fst))
      continuous_snd
  let B := (T ×ˢ S) ∩ graph
  have hB : IsCompact B := (hT.prod hS).inter_right hGraph
  have heq :
      (fun p : H × X => recover p.1 p.2) '' B =
        (Units.val : G → M) '' {h : G | ∃ g ∈ T, rowPoint h.val g ∈ S} := by
    ext h
    constructor
    · rintro ⟨⟨g, x⟩, ⟨⟨hg, hx⟩, hrow⟩, rfl⟩
      have hr : rowPoint (recover g x) g = x := hrow
      have hu : IsUnit (recover g x) :=
        isUnit_of_hasFullRowRank (hr ▸ hRank x hx)
      refine ⟨hu.unit, ⟨g, hg, ?_⟩, hu.unit_spec⟩
      rw [hu.unit_spec, hr]
      exact hx
    · rintro ⟨u, ⟨g, hg, hrow⟩, rfl⟩
      refine ⟨(g, rowPoint u.val g), ⟨⟨hg, hrow⟩, ?_⟩, recover_rowPoint _ _⟩
      change rowPoint (recover g (rowPoint u.val g)) g = rowPoint u.val g
      rw [recover_rowPoint]
  apply Units.isOpenEmbedding_val.isEmbedding.isCompact_iff.mpr
  rw [← heq]
  exact hB.image continuous_recover

private theorem hasCompactSupport_pullback (g : H) {S : Set X} (hS : IsCompact S)
    (hRank : ∀ x ∈ S, HasFullRowRank x) (Φ : X → ℂ) (hΦ : ∀ x ∉ S, Φ x = 0) :
    HasCompactSupport (fun h : G => Φ (rowPoint h.val g)) := by
  have hK := isCompact_support_preimage (isCompact_singleton (x := g)) hS hRank
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro h hh
  refine ⟨g, mem_singleton _, ?_⟩
  by_contra hns
  exact hh (hΦ _ hns)

/-- Full-row-rank compact support makes the real Godement inner integral entire
in the complex exponent of any continuous real weight. -/
def RealGodementCompactSupportStatement : Prop :=
  ∀ (m : ℕ) [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ]
    (g : Langlands.GeneralLinear (m + 1) ℝ)
    (S : Set (Matrix (Fin m) (Fin (m + 1)) ℝ)),
    IsCompact S → (∀ x ∈ S, HasFullRowRank x) →
  ∀ (Φ : Matrix (Fin m) (Fin (m + 1)) ℝ → ℂ)
    (η : Langlands.GeneralLinear m ℝ → ℂ) (L : Langlands.GeneralLinear m ℝ → ℝ),
    Continuous Φ → (∀ x ∉ S, Φ x = 0) → Continuous η → Continuous L →
      (∀ s : ℂ, Integrable (fun h => Φ (rowPoint h.val g) * η h *
        Complex.exp (s * (L h : ℂ))) μ) ∧
      Differentiable ℂ (fun s : ℂ => ∫ h, Φ (rowPoint h.val g) * η h *
        Complex.exp (s * (L h : ℂ)) ∂μ)

theorem realGodementCompactSupport : RealGodementCompactSupportStatement := by
  intro m _ _ μ _ g S hS hRank Φ η L hΦ hΦS hη hL
  let A := fun h : Langlands.GeneralLinear m ℝ => Φ (rowPoint h.val g) * η h
  have hA : Continuous A :=
    (hΦ.comp (continuous_rowPoint.comp
      (Units.continuous_val.prodMk continuous_const))).mul hη
  have hSupport : HasCompactSupport A := (hasCompactSupport_pullback g hS hRank Φ hΦS).mul_right
  have hInt (σ : ℝ) : Integrable (fun h => ‖A h‖ * Real.exp (σ * L h)) μ :=
    (hA.norm.mul (Real.continuous_exp.comp (hL.const_mul σ))).integrable_of_hasCompactSupport
      hSupport.norm.mul_right
  exact ⟨UnequalAnalytic.integrable_mul_cexp hA.aestronglyMeasurable hL.aestronglyMeasurable hInt,
    UnequalAnalytic.differentiable_integral_mul_cexp
      hA.aestronglyMeasurable hL.aestronglyMeasurable hInt⟩

end Langlands.Global.RankinSelbergGlobal.RealGodement
