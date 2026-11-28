import Langlands.Representation.Archimedean.SmoothDerivativeTopology
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! # Factoring smooth functionals through finitely many genuine derivatives -/

noncomputable section

open scoped ContDiff Manifold NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

/-- A continuous scalar form on the genuine smooth carrier is obtained from a bounded
form on a finite product of the original representation space by taking word derivatives. -/
def SmoothDerivativeFunctionalStatement : Prop :=
  ∀ {A H G E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace H]
    (I : ModelWithCorners ℝ A H) [Group G] [TopologicalSpace G] [ChartedSpace H G] [LieGroup I ∞ G]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (R : G →* (E →L[ℂ] E))
    (L : DerivativeSmoothVectors I R →L[ℂ] ℂ),
    ∃ (J : Finset (List A)) (T : (J → E) →L[ℂ] ℂ),
      ∀ v : DerivativeSmoothVectors I R, L v = T (fun X => derivativeCoordinates I R v X.val)

set_option maxHeartbeats 450000 in
theorem smoothDerivativeFunctional : SmoothDerivativeFunctionalStatement := by
  intro A H G E _ _ _ I _ _ _ _ _ _ R L
  classical
  let D := DerivativeSmoothVectors I R
  let q : Seminorm ℂ D := (normSeminorm ℂ ℂ).comp L.toLinearMap
  have hq : Continuous q := L.continuous.norm
  obtain ⟨J, c, _, hBound⟩ := Seminorm.bound_of_continuous (withSeminorms_wordSeminormFamily I R) q hq
  let C : D →ₗ[ℂ] (J → E) := LinearMap.pi fun X =>
    (LinearMap.proj X.val).comp (derivativeCoordinates I R)
  have hC (v : D) : ‖L v‖ ≤ (c : ℝ) * ‖C v‖ := by
    have h := Seminorm.le_def.mp hBound v
    rw [smul_apply, NNReal.smul_def, smul_eq_mul] at h
    change ‖L v‖ ≤ _ at h
    refine h.trans (mul_le_mul_of_nonneg_left ?_ c.coe_nonneg)
    refine Seminorm.finset_sup_apply_le (norm_nonneg _) fun X hX => ?_
    rw [wordSeminormFamily_apply]
    rw [← derivativeCoordinates_apply]
    exact norm_le_pi_norm (C v) (⟨X, hX⟩ : J)
  have hKer : LinearMap.ker C ≤ LinearMap.ker L.toLinearMap := by
    intro v hv
    have hz := hC v
    rw [LinearMap.mem_ker.mp hv, norm_zero, mul_zero] at hz
    exact LinearMap.mem_ker.mpr (norm_le_zero_iff.mp hz)
  let P := LinearMap.range C
  let L₀ : P →ₗ[ℂ] ℂ := ((LinearMap.ker C).liftQ L.toLinearMap hKer).comp C.quotKerEquivRange.symm.toLinearMap
  have he (v : D) : L₀ ⟨C v, ⟨v, rfl⟩⟩ = L v := by
    change ((LinearMap.ker C).liftQ L.toLinearMap hKer)
      (C.quotKerEquivRange.symm ⟨C v, ⟨v, rfl⟩⟩) = L v
    rw [C.quotKerEquivRange_symm_apply_image v]
    rfl
  let L₁ : P →L[ℂ] ℂ := L₀.mkContinuous c fun x => by
    obtain ⟨v, hv⟩ := x.property
    have hx : (⟨C v, ⟨v, rfl⟩⟩ : P) = x := Subtype.ext hv
    rw [← hx, he]
    exact hC v
  obtain ⟨T, hT, _⟩ := exists_extension_norm_eq P L₁
  refine ⟨J, T, fun v => ?_⟩
  change L v = T (C v)
  exact (he v).symm.trans (hT ⟨C v, ⟨v, rfl⟩⟩).symm

end Langlands.Archimedean.DerivativeSmoothVectors
