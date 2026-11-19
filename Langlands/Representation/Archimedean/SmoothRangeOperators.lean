import Langlands.Representation.Archimedean.SmoothUnitActionDerivative
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Continuity of bounded operators with genuine smooth ranges -/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.DerivativeSmoothVectors

open Langlands.Analysis (hasDerivAt_iff_tendsto_slope_tvs)

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [FiniteDimensional ℝ A] {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
  (R : Aˣ →* (E →L[ℂ] E))

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R

private def smoothRangeLinear (T : B →L[ℂ] E) (hT : ∀ v, IsSmoothVector 𝓜 R (T v)) :
    B →ₗ[ℂ] D :=
  (toSmooth 𝓜 R).symm.toLinearMap.comp
    (T.toLinearMap.codRestrict (smoothVectors 𝓜 R) hT)

private theorem exists_clm_lieDerivative_comp (hR : IsContinuousRepresentation R)
    (T : B →L[ℂ] E) (hT : ∀ v, IsSmoothVector 𝓜 R (T v)) (X : A) :
    ∃ L : B →L[ℂ] E, ∀ v, L v = lieDerivative 𝓜 R X (T v) := by
  let lift := smoothRangeLinear R T hT
  let L : B →ₗ[ℂ] E := (derivativeCLM 𝓜 R []).toLinearMap.comp ((operator 𝓜 R X).comp lift)
  let τ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let γ : ℝ → A := fun t => 1 + t • X
  let S : ℕ → B →L[ℂ] E := fun n =>
    (τ n)⁻¹ • ((R ((unitsValueChart A).symm (γ (τ n)))).comp T - T)
  have hτ : Tendsto τ atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by change τ n ≠ 0; dsimp [τ]; positivity⟩
  have hγ : HasDerivAt γ X 0 := by
    simpa only [γ, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add 1
  have hlim (v : B) : Tendsto (fun n => S n v) atTop (𝓝 (L v)) := by
    have hd : HasDerivAt (fun t => unitsChartAction R (γ t, lift v))
        (operator 𝓜 R X (lift v)) 0 := by
      simpa only [inv_one, Units.val_one, one_mul, map_one, Module.End.one_apply] using
        hasDerivAt_unitsChartOrbit R hR (1 : Aˣ) (lift v) hγ (by simp [γ])
    let P := (derivativeCLM 𝓜 R []).restrictScalars ℝ
    have h := ((P.continuous.tendsto (operator 𝓜 R X (lift v))).comp
      (hasDerivAt_iff_tendsto_slope_tvs.mp hd)).comp hτ
    refine h.congr (fun n => ?_)
    have h0 : P (unitsChartAction R (γ 0, lift v)) = T v := by
      change P (unitsChartAction R (1 + (0 : ℝ) • X, lift v)) = _
      rw [zero_smul, add_zero]
      change P (unitsChartAction R ((1 : Aˣ).val, lift v)) = _
      rw [unitsChartAction_val, map_one, Module.End.one_apply]
      rfl
    change P (slope (fun t => unitsChartAction R (γ t, lift v)) 0 (τ n)) = S n v
    rw [slope_def_module, sub_zero, map_smul, map_sub, h0]
    rfl
  obtain ⟨C, hC⟩ := banach_steinhaus (g := S) fun v => by
    obtain ⟨b, hb⟩ := (Metric.isBounded_range_of_tendsto _ (hlim v)).exists_norm_le
    exact ⟨b, fun n => hb (S n v) ⟨n, rfl⟩⟩
  have hb (v : B) : ‖L v‖ ≤ C * ‖v‖ :=
    le_of_tendsto' (hlim v).norm fun n =>
      ((S n).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg v))
  exact ⟨L.mkContinuous C hb, fun v => rfl⟩

private theorem exists_clm_word_comp (hR : IsContinuousRepresentation R)
    (T : B →L[ℂ] E) (hT : ∀ v, IsSmoothVector 𝓜 R (T v)) (s : List A) :
    ∃ L : B →L[ℂ] E, ∀ v, L v = derivativeCoordinates 𝓜 R (smoothRangeLinear R T hT v) s := by
  induction s with
  | nil => exact ⟨T, fun v => rfl⟩
  | cons X s ih =>
      obtain ⟨L, hL⟩ := ih
      have hsm (v : B) : IsSmoothVector 𝓜 R (L v) := by
        rw [hL]
        exact (smoothIteratedLieDerivative 𝓜 R s (toSmooth 𝓜 R
          (smoothRangeLinear R T hT v))).property
      obtain ⟨M, hM⟩ := exists_clm_lieDerivative_comp R hR L hsm X
      refine ⟨M, fun v => ?_⟩
      rw [hM, hL, derivativeCoordinates_apply, derivativeCoordinates_apply, iteratedLieDerivative_cons]

/-- A bounded operator with smooth range is continuous into the genuine derivative topology. -/
def smoothRangeCLM (hR : IsContinuousRepresentation R)
    (T : B →L[ℂ] E) (hT : ∀ v, IsSmoothVector 𝓜 R (T v)) : B →L[ℂ] D where
  toLinearMap := smoothRangeLinear R T hT
  cont := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro s
    obtain ⟨L, hL⟩ := exists_clm_word_comp R hR T hT s
    exact L.continuous.congr hL

@[simp]
theorem smoothRangeCLM_empty (hR : IsContinuousRepresentation R)
    (T : B →L[ℂ] E) (hT : ∀ v, IsSmoothVector 𝓜 R (T v)) (v : B) :
    derivativeCoordinates 𝓜 R (smoothRangeCLM R hR T hT v) [] = T v :=
  rfl

end Langlands.Archimedean.DerivativeSmoothVectors
