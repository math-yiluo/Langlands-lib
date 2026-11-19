import Langlands.Analysis.CompactLinearParameterIntegralProof
import Langlands.Global.RankinSelberg.RealGodementCompactSupport

/-! # Smoothness of real Godement integrals with compact full-row-rank support -/

noncomputable section

open Langlands.Archimedean MeasureTheory Metric Set
open scoped Matrix.Norms.Operator Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "Y" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ

private def rowsLinear (h : M) : Y →L[ℝ] X :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => h * lastRows g
      map_add' := fun g g' => by
        rw [show lastRows (g + g') = lastRows g + lastRows g' from rfl, Matrix.mul_add]
      map_smul' := fun c g => by
        rw [show lastRows (c • g) = c • lastRows g from rfl, Matrix.mul_smul]
        rfl }

private def parameterOperator : M →ₗ[ℝ] Y →L[ℝ] X where
  toFun := rowsLinear
  map_add' h h' := ContinuousLinearMap.ext fun g => Matrix.add_mul h h' (lastRows g)
  map_smul' c h := ContinuousLinearMap.ext fun g => Matrix.smul_mul c h (lastRows g)

private theorem continuous_parameterOperator : Continuous (fun h : G => rowsLinear h.val) :=
  (LinearMap.toContinuousLinearMap (parameterOperator (m := m))).continuous.comp
    (show Continuous (Units.val : G → M) from Units.continuous_val)

private theorem isCompact_val_preimage {T : Set Y} (hT : IsCompact T)
    (hUnit : ∀ a ∈ T, IsUnit a) :
    IsCompact ((Units.val : H → Y) ⁻¹' T) := by
  apply Units.isOpenEmbedding_val.isEmbedding.isCompact_iff.mpr
  have heq : (Units.val : H → Y) '' ((Units.val : H → Y) ⁻¹' T) = T := by
    apply Set.Subset.antisymm (Set.image_preimage_subset _ _)
    intro a ha
    obtain ⟨g, rfl⟩ := hUnit a ha
    exact ⟨g, ha, rfl⟩
  rw [heq]
  exact hT

section Integral

variable [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
  [BorelSpace (Langlands.GeneralLinear m ℝ)]
  (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ]

/-- The real Godement inner integral with an arbitrary continuous multiplier. -/
def innerIntegral (Φ : X → ℂ) (η : G → ℂ) (g : H) : ℂ :=
  ∫ h, η h * Φ (rowPoint h.val g) ∂μ

private theorem contDiffOn_innerIntegral {S : Set X} (hS : IsCompact S)
    (hRank : ∀ x ∈ S, HasFullRowRank x) {Φ : X → ℂ} (hΦ : ContDiff ℝ ∞ Φ)
    (hΦS : ∀ x ∉ S, Φ x = 0) {η : G → ℂ} (hη : Continuous η) :
    ContDiffOn ℝ ∞ (fun a : Y => ∫ h, η h * Φ (rowsLinear h.val a) ∂μ)
      {a : Y | IsUnit a} := by
  intro a ha
  obtain ⟨ε, hε, hBall⟩ :=
    Metric.isOpen_iff.1 (isOpen_setOf_isUnit_matrix (F := ℝ) (N := m + 1)) a ha
  let T := (Units.val : H → Y) ⁻¹' closedBall a (ε / 2)
  have hT : IsCompact T :=
    isCompact_val_preimage (isCompact_closedBall _ _) fun b hb =>
      hBall (closedBall_subset_ball (half_lt_self hε) hb)
  let V := {h : G | ∃ g ∈ T, rowPoint h.val g ∈ S}
  have hV : IsCompact V := isCompact_support_preimage hT hS hRank
  have hSmooth := (Langlands.Analysis.compactLinearParameterIntegral G Y X μ V hV
    univ isOpen_univ univ isOpen_univ η hη (fun h => rowsLinear h.val)
    continuous_parameterOperator Φ hΦ.contDiffOn (fun _ _ _ _ => mem_univ _)).1
  have hNear :
      (fun b : Y => ∫ h, η h * Φ (rowsLinear h.val b) ∂μ) =ᶠ[nhds a]
      (fun b : Y => ∫ h in V, η h * Φ (rowsLinear h.val b) ∂μ) := by
    filter_upwards [ball_mem_nhds a (half_pos hε)] with b hb
    have hbc : b ∈ closedBall a (ε / 2) := ball_subset_closedBall hb
    obtain ⟨g, rfl⟩ : IsUnit b := hBall (closedBall_subset_ball (half_lt_self hε) hbc)
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => ?_).symm
    have hn : rowPoint h.val g ∉ S := fun hS' => hh ⟨g, hbc, hS'⟩
    change η h * Φ (rowPoint h.val g) = 0
    rw [hΦS _ hn, mul_zero]
  exact ((hSmooth.contDiffAt (by simp)).congr_of_eventuallyEq hNear).contDiffWithinAt

/-- Smoothness of the compactly supported real Godement integral in the translating
matrix, for a smooth test function and a continuous multiplier. -/
def RealGodementSmoothStatement : Prop :=
  ∀ (m : ℕ) [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ]
    (S : Set (Matrix (Fin m) (Fin (m + 1)) ℝ)), IsCompact S →
    (∀ x ∈ S, HasFullRowRank x) →
    ∀ (Φ : Matrix (Fin m) (Fin (m + 1)) ℝ → ℂ)
      (η : Langlands.GeneralLinear m ℝ → ℂ),
      ContDiff ℝ ∞ Φ → (∀ x ∉ S, Φ x = 0) → Continuous η →
      ContMDiff (matrixModel ℝ (m + 1)) 𝓘(ℝ, ℂ) ∞ (innerIntegral μ Φ η)

theorem realGodementSmooth : RealGodementSmoothStatement := by
  intro m _ _ μ _ S hS hRank Φ η hΦ hΦS hη
  exact contMDiff_of_contDiffOn (contDiffOn_innerIntegral μ hS hRank hΦ hΦS hη) (fun _ => rfl)

end Integral

end Langlands.Global.RankinSelbergGlobal.RealGodement
