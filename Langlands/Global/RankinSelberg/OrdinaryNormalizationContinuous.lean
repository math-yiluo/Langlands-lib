import Langlands.Analysis.IntegrableLinearKernelContinuity
import Langlands.Analysis.LandauDirichlet
import Langlands.Global.RankinSelberg.OrdinaryNormalizationLinear
import Langlands.Global.RankinSelberg.RealSmoothNormalizedEvaluationContinuity

/-! # Continuous evaluations of entire linear integral normalizations -/

noncomputable section

open MeasureTheory Set
open Langlands.LocalFactor

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Analysis (integrableLinearKernelContinuity)
open Langlands.GeneralDirichlet (eqOn_halfPlane)
open RealSmoothNormalizedEvaluationContinuity (continuous_eval_of_entire)

variable {V X : Type*} [AddCommGroup V] [Module ℂ V] [UniformSpace V]
  [IsUniformAddGroup V] [ContinuousSMul ℂ V] [SequentialSpace V] [BarrelledSpace ℂ V]
  [MeasurableSpace X]

/-- Linear pointwise continuous integrands with common absolute convergence and holomorphy
on a right half-plane give continuous evaluations of all their entire normalized values. -/
def OrdinaryNormalizationContinuousStatement : Prop :=
  ∀ (μ : Measure X) (K : ℂ → X → V →L[ℂ] ℂ) (L : ReciprocalEntire) (σ : ℝ),
    (∃ b : ℝ, ∀ s : ℂ, b < s.re → L.denominator s ≠ 0) →
    (∀ v s, σ < s.re → Integrable (fun x => K s x v) μ) →
    (∀ v, DifferentiableOn ℂ (fun s => ∫ x, K s x v ∂μ) {s : ℂ | σ < s.re}) →
    (∀ v, Nonempty (OrdinaryIntegralNormalization (fun s => ∫ x, K s x v ∂μ)
      (fun s => (L.denominator s)⁻¹))) →
    ∃ A : V →ₗ[ℂ] (ℂ → ℂ),
      (∀ v, Differentiable ℂ (A v) ∧ ∀ s, σ < s.re →
        A v s = L.denominator s * ∫ x, K s x v ∂μ) ∧
      ∀ s, Continuous (fun v => A v s)

theorem ordinaryNormalizationContinuous : OrdinaryNormalizationContinuousStatement (V := V) (X := X) := by
  intro μ K L σ hL hI hHol hNorm
  classical
  let N := fun v => (hNorm v).some
  let raw : V →ₗ[ℂ] (ℂ → X → ℂ) :=
    { toFun := fun v s x => K s x v
      map_add' v w := by ext s x; exact (K s x).map_add v w
      map_smul' c v := by ext s x; exact (K s x).map_smul c v }
  obtain ⟨b, hb⟩ := hL
  obtain ⟨A, hA⟩ := ordinaryNormalizationLinear μ raw (fun s => (L.denominator s)⁻¹)
    ⟨b, fun s hs => inv_ne_zero (hb s hs)⟩ (fun v => ⟨σ, hI v⟩) N
  have hD (v : V) : Differentiable ℂ (A v) := by
    rw [hA]
    exact fun s => ((N v).analytic s (mem_univ s)).differentiableAt
  have hRight (v : V) : ∀ s, σ < s.re → A v s = L.denominator s * ∫ x, K s x v ∂μ := by
    obtain ⟨c, hc⟩ := (N v).eq_on_right
    refine fun s hs => eqOn_halfPlane (hD v).differentiableOn (L.entire.differentiableOn.mul (hHol v))
      (σ₁ := max b c) (fun z hz => ?_) hs
    change A v z = L.denominator z * ∫ x, K z x v ∂μ
    rw [hA, hc z ((le_max_right _ _).trans_lt hz), mul_comm ((N v).value z), ← mul_assoc,
      mul_inv_cancel₀ (hb z ((le_max_left _ _).trans_lt hz)), one_mul]
  refine ⟨A, fun v => ⟨hD v, hRight v⟩, ?_⟩
  have hNonempty : {z : ℂ | σ < z.re}.Nonempty := ⟨(σ + 1 : ℝ), by simp⟩
  apply continuous_eval_of_entire A hD (isOpen_lt continuous_const Complex.continuous_re) hNonempty
  intro z hz
  obtain ⟨_, J, hJ⟩ := integrableLinearKernelContinuity μ (K z) (hI · z hz)
  have he (v : V) : A v z = L.denominator z * J v := by rw [hJ, hRight v z hz]
  rw [funext he]
  exact continuous_const.mul J.continuous

end Langlands.Global.RankinSelbergGlobal
