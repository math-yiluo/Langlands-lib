import Langlands.Analysis.SchwartzCompactEvaluation
import Langlands.Global.RankinSelberg.RealGodementSmooth
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Local compact supports for the real Godement test orbit -/

noncomputable section

open Langlands.Archimedean Langlands.Analysis.SchwartzCompactFamilies
open MeasureTheory Set
open scoped ContDiff Matrix.Norms.Operator SchwartzMap Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "Y" => Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ

private def rectangularMul : X →L[ℝ] Y →L[ℝ] X :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => (mulLeftLinearMap (Fin (m + 1)) ℝ x).toContinuousLinearMap
      map_add' := fun x y => ContinuousLinearMap.ext fun A => Matrix.add_mul x y A
      map_smul' := fun c x => ContinuousLinearMap.ext fun A => Matrix.smul_mul c x A }

private theorem contDiff_rectangularMul : ContDiff ℝ ∞ (fun p : Y × X => p.2 * p.1) :=
  ((rectangularMul (m := m)).contDiff.comp contDiff_snd).clm_apply contDiff_fst

/-- Around an invertible parameter there is a single compact set of full-row-rank
matrices supporting the whole right pullback family. -/
def RealGodementCompactOrbitStatement : Prop :=
  ∀ (S : Set X), IsCompact S → (∀ x ∈ S, HasFullRowRank x) →
    ∀ (Φ : 𝓢(X, ℂ)), (∀ x ∉ S, Φ x = 0) → ∀ (g : H),
      ∃ (U : Set Y) (T : Set X),
        IsOpen U ∧ g.val ∈ U ∧ (∀ A ∈ U, IsUnit A) ∧ IsCompact T ∧ S ⊆ T ∧
        (∀ x ∈ T, HasFullRowRank x) ∧
        ∃ Q : Y → supportedSchwartz T, ∀ A ∈ U, ∀ x, (Q A).val x = Φ (x * A)

theorem realGodementCompactOrbit : RealGodementCompactOrbitStatement (m := m) := by
  classical
  intro S hS hRank Φ hΦ g
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.1
    (isOpen_setOf_isUnit_matrix (F := ℝ) (N := m + 1)) g.val g.isUnit
  let U := Metric.ball g.val (ε / 2)
  let K := (Units.val : H → Y) ⁻¹' Metric.closedBall g.val (ε / 2)
  have hClosed : ∀ A ∈ Metric.closedBall g.val (ε / 2), IsUnit A :=
    fun A hA => hBall (Metric.closedBall_subset_ball (half_lt_self hε) hA)
  have hUnit : ∀ A ∈ U, IsUnit A := fun A hA => hClosed A (Metric.ball_subset_closedBall hA)
  have hK : IsCompact K := isCompact_val_preimage (isCompact_closedBall _ _) hClosed
  let f : X × H → X := fun p => p.1 * (p.2⁻¹).val
  have hf : Continuous f := continuous_fst.matrix_mul (Units.continuous_coe_inv.comp continuous_snd)
  let T := S ∪ f '' (S ×ˢ K)
  refine ⟨U, T, Metric.isOpen_ball, Metric.mem_ball_self (half_pos hε), hUnit,
    hS.union ((hS.prod hK).image hf), subset_union_left, ?_, ?_⟩
  · rintro x (hx | ⟨⟨y, q⟩, ⟨hy, _⟩, rfl⟩)
    · exact hRank x hx
    · obtain ⟨R, hR⟩ := hRank y hy
      refine ⟨q.val * R, ?_⟩
      change (y * (q⁻¹).val) * (q.val * R) = 1
      rw [Matrix.mul_assoc y, ← Matrix.mul_assoc (q⁻¹).val, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul, hR]
  · have hSupport (A : Y) (hA : A ∈ U) (x : X) (hx : x ∉ T) : Φ (x * A) = 0 := by
      apply hΦ
      obtain ⟨q, rfl⟩ := hUnit A hA
      intro hxS
      apply hx
      right
      refine ⟨(x * q.val, q), ⟨hxS, Metric.ball_subset_closedBall hA⟩, ?_⟩
      change (x * q.val) * (q⁻¹).val = x
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    let Q (A : Y) : supportedSchwartz T := if hA : A ∈ U then
      ⟨ofCompactSupport (fun x => Φ (x * A)) ((Φ.smooth ⊤).comp
          (contDiff_rectangularMul.comp (contDiff_const.prodMk contDiff_id))) T
          (hS.union ((hS.prod hK).image hf)) (hSupport A hA), hSupport A hA⟩
      else 0
    refine ⟨Q, fun A hA x => ?_⟩
    simp only [Q, dite_eq_left hA, ofCompactSupport_apply]

/-- The Schwartz representative of the first variation of the right pullback at the identity. -/
def rectangularRightVariation (Φ : 𝓢(X, ℂ)) (B : Y) (S : Set X) (hS : IsCompact S)
    (hΦ : ∀ x ∉ S, Φ x = 0) : supportedSchwartz S := by
  let ψ := fun x : X => fderiv ℝ (⇑Φ) x (x * B)
  have hψ : ContDiff ℝ ∞ ψ :=
    ((Φ.smooth ⊤).fderiv_right (by simp)).clm_apply
      ((rectangularMul (m := m)).contDiff.clm_apply contDiff_const)
  have hZero : ∀ x ∉ S, ψ x = 0 := by
    intro x hx
    have hS' : tsupport (⇑Φ) ⊆ S := by
      apply closure_minimal _ hS.isClosed
      intro y hy
      by_contra h
      exact hy (hΦ y h)
    change fderiv ℝ (⇑Φ) x (x * B) = 0
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hx (hS' h))]
    rfl
  exact ⟨ofCompactSupport ψ hψ S hS hZero, hZero⟩

@[simp] theorem rectangularRightVariation_apply (Φ : 𝓢(X, ℂ)) (B : Y) (S : Set X)
    (hS : IsCompact S) (hΦ : ∀ x ∉ S, Φ x = 0) (x : X) :
    (rectangularRightVariation Φ B S hS hΦ).val x = fderiv ℝ (⇑Φ) x (x * B) := rfl

/-- Scalar evaluation on the orbit differentiates by the compact test variation. -/
theorem compactOrbit_evaluation {S : Set X} (hS : IsCompact S)
    (L : supportedSchwartz S →ₗ[ℂ] ℂ) (q : Seminorm ℝ 𝓢(X, ℂ)) (hq : Continuous q)
    (hBound : ∀ f : supportedSchwartz S, ‖L f‖ ≤ q f.val)
    {U : Set Y} (hU : IsOpen U) (Q : Y → supportedSchwartz S) (Φ : 𝓢(X, ℂ))
    (hQ : ∀ A ∈ U, ∀ x, (Q A).val x = Φ (x * A)) :
    ContDiffOn ℝ ∞ (fun A => L (Q A)) U ∧
    ∀ (_ : (1 : Y) ∈ U) (B : Y) (hΦ : ∀ x ∉ S, Φ x = 0),
      fderiv ℝ (fun A => L (Q A)) 1 B = L (rectangularRightVariation Φ B S hS hΦ) := by
  have hF : ContDiff ℝ ∞ (fun p : Y × X => Φ (p.2 * p.1)) :=
    (Φ.smooth ⊤).comp contDiff_rectangularMul
  obtain ⟨hSmooth, hDeriv⟩ := schwartzCompactEvaluation Y X S hS L q hq hBound U hU Q _ hQ hF
  refine ⟨hSmooth, fun h₁ B hΦ => hDeriv 1 h₁ B _ (fun x => ?_)⟩
  let M : Y →L[ℝ] X := rectangularMul x
  have hD := ((Φ.smooth ⊤).differentiable (by simp) (M 1)).hasFDerivAt.comp 1 M.hasFDerivAt
  have hEq : M 1 = x := Matrix.mul_one _
  rw [rectangularRightVariation_apply]
  change fderiv ℝ (⇑Φ) x (M B) = fderiv ℝ (fun A => Φ (M A)) 1 B
  rw [show fderiv ℝ (fun A => Φ (M A)) 1 = (fderiv ℝ (⇑Φ) (M 1)).comp M from hD.fderiv,
    ContinuousLinearMap.comp_apply, hEq]

end Langlands.Global.RankinSelbergGlobal.RealGodement
