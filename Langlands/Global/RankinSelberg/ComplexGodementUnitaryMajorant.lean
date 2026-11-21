import Langlands.Analysis.EuclideanBallCutoff
import Langlands.Global.RankinSelberg.ComplexGodementFourier
import Langlands.Global.RankinSelberg.SchwartzRapidMajorant
import Langlands.Representation.Archimedean.ComplexLastRowIntegral
import Langlands.Representation.Archimedean.ComplexMaximalParabolicIntegration

/-! # A right-unitary-invariant Schwartz majorant for complex matrix tests -/

noncomputable section

open scoped ContDiff Matrix.Norms.Operator RealInnerProductSpace SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean.ComplexLastRowIntegral (sqNorm_vecMul)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (mul_conjTranspose_one)
open Langlands.Analysis (ballCutoff ballCutoff_apply ballCutoff_nonneg ballCutoff_eq_one
  contDiff_ballCutoff hasCompactSupport_ballCutoff)
open ComplexGodementFourier (curryLinearEquiv)
open SchwartzMajorant (exists_nonneg_schwartz_majorant_of_bump)

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin m) (Fin n) ℂ
local notation "E" => EuclideanSpace ℂ (Fin m × Fin n)

private def matrixEuclidean : Mat ≃L[ℝ] E :=
  ((curryLinearEquiv (Fin m) (Fin n) ℝ ℂ).symm.trans
    (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℂ)).symm).toContinuousLinearEquiv

private theorem matrixEuclidean_norm_sq (X : Mat) :
    ‖matrixEuclidean X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

private theorem matrixEuclidean_norm_mul_unitary (X : Mat) (k : unitaryCompact ℂ n) :
    ‖matrixEuclidean (X * k.val.val)‖ = ‖matrixEuclidean X‖ := by
  have h : ‖matrixEuclidean (X * k.val.val)‖ ^ 2 = ‖matrixEuclidean X‖ ^ 2 := by
    rw [matrixEuclidean_norm_sq, matrixEuclidean_norm_sq]
    exact Finset.sum_congr rfl fun i _ => sqNorm_vecMul (mul_conjTranspose_one k) (X i)
  simpa only [Real.sqrt_sq (norm_nonneg _)] using congrArg Real.sqrt h

/-- The absolute value of any rectangular Schwartz test on complex matrices is
dominated by a real Schwartz test invariant under right unitary multiplication. -/
def ComplexGodementUnitaryMajorantStatement : Prop :=
  ∀ (m n : ℕ) (Φ : 𝓢(Matrix (Fin m) (Fin n) ℂ, ℂ)),
    ∃ Ψ : 𝓢(Matrix (Fin m) (Fin n) ℂ, ℝ),
      (∀ X, ‖Φ X‖ ≤ Ψ X) ∧
      ∀ (X : Matrix (Fin m) (Fin n) ℂ) (k : unitaryCompact ℂ n), Ψ (X * k.val.val) = Ψ X

theorem complexGodementUnitaryMajorant : ComplexGodementUnitaryMajorantStatement := by
  intro m n Φ
  let V := EuclideanSpace ℂ (Fin m × Fin n)
  let e := matrixEuclidean (m := m) (n := n)
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm Φ
  let b₀ := ballCutoff (0 : V) 1 2
  have hb₀c : HasCompactSupport b₀ :=
    hasCompactSupport_ballCutoff (x₀ := (0 : V)) (ρ := 1) (R := 2) (by norm_num) (by norm_num)
  let b : 𝓢(V, ℝ) := hb₀c.toSchwartzMap (contDiff_ballCutoff 0 1 2)
  have hbnon : ∀ x, 0 ≤ b x := ballCutoff_nonneg (0 : V) 1 2
  have hbone (x : V) (hx : ‖x‖ ≤ 1) : b x = 1 :=
    ballCutoff_eq_one (x₀ := (0 : V)) (ρ := 1) (R := 2) (by norm_num) (by norm_num)
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  have hrapid (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : V, (1 + ‖x‖) ^ N * ‖F x‖ ≤ C := by
    refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun p => SchwartzMap.seminorm ℝ p.1 p.2) F,
      mul_nonneg (by positivity) (apply_nonneg _ _), fun x => ?_⟩
    simpa only [norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (le_refl N) (le_refl 0) F x
  obtain ⟨P, _, hP, hEq⟩ :=
    exists_nonneg_schwartz_majorant_of_bump b hbnon hbone id (fun x => ‖F x‖) (fun _ => norm_nonneg _) hrapid
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e P, ?_, fun X k => ?_⟩
  · intro X
    have h := hP (e X)
    change ‖Φ (e.symm (e X))‖ ≤ P (e X) at h
    change ‖Φ X‖ ≤ P (e X)
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using h
  · change P (e (X * k.val.val)) = P (e X)
    apply hEq
    intro R _
    change b₀ (R⁻¹ • e (X * k.val.val)) = b₀ (R⁻¹ • e X)
    have hk : ‖e (X * k.val.val)‖ = ‖e X‖ := matrixEuclidean_norm_mul_unitary X k
    simp only [b₀, ballCutoff_apply, sub_zero, norm_smul, hk]

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
