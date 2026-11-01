import Langlands.Global.ArchimedeanCompactCoefficientAverage
import Langlands.Representation.CompactCharacterReproduction

/-! # Character averaging fixes the actual algebraic compact-type span -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL.CompactWeightedAverage

open MeasureTheory DerivativeSmoothFunctions
open scoped BigOperators

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}
  [MeasurableSpace (standardInfiniteCompact K n)]
  [BorelSpace (standardInfiniteCompact K n)]
  (ν : Measure (standardInfiniteCompact K n))
  [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]

/-- Scalar evaluation transfers source reproduction through any actual intertwiner. -/
theorem characterAverage_intertwiner (σ : CompactType K n)
    (I : σ.toRepresentation.IntertwiningMap (compactAction K n))
    (v : Fin σ.dim → ℂ) :
    characterAverage ν σ.toContinuousCompactRep (I v) = I v := by
  apply (toSmooth K n).injective
  apply Subtype.ext
  funext x
  suffices evalCLM K n x (characterAverage ν σ.toContinuousCompactRep (I v)) =
      evalCLM K n x (I v) by
    simpa only [evalCLM_apply] using this
  let L : (Fin σ.dim → ℂ) →L[ℂ] ℂ :=
    ((evalCLM K n x).toLinearMap.comp I.toLinearMap).toContinuousLinearMap
  have hs := congrArg L
    (Langlands.Representation.CompactSchur.inverseCharacter_reproduces
      σ.toRepresentation σ.continuous_action σ.isIrreducible ν v)
  rw [map_smul, ← L.integral_comp_comm
    (Langlands.Representation.CompactSchur.inverseCharacter_integrable
      σ.toRepresentation σ.continuous_action ν v)] at hs
  simp only [map_smul, smul_eq_mul] at hs
  have he (k : standardInfiniteCompact K n) :
      evalCLM K n (x * k.val) (I v) = L (σ.toRepresentation k v) := by
    change _ = evalCLM K n x (I (σ.toRepresentation k v))
    rw [I.isIntertwining, compactAction_apply, evalCLM_rightAction]
  rw [characterAverage, eval_averageCLM]
  change (∫ k : standardInfiniteCompact K n,
    characterWeight σ.toContinuousCompactRep k *
      evalCLM K n (x * k.val) (I v) ∂ν) = L v
  calc
    (∫ k : standardInfiniteCompact K n,
        characterWeight σ.toContinuousCompactRep k *
          evalCLM K n (x * k.val) (I v) ∂ν) =
      ∫ k : standardInfiniteCompact K n, (σ.dim : ℂ) *
        (Matrix.trace (LinearMap.toMatrix' (σ.toRepresentation k⁻¹)) *
          L (σ.toRepresentation k v)) ∂ν := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro k
      dsimp only
      rw [characterWeight_apply, he, mul_assoc]
    _ = (σ.dim : ℂ) * (∫ k : standardInfiniteCompact K n,
        Matrix.trace (LinearMap.toMatrix' (σ.toRepresentation k⁻¹)) *
          L (σ.toRepresentation k v) ∂ν) := integral_const_mul _ _
    _ = L v := hs

/-- The character average fixes the whole published algebraic compact-type submodule. -/
theorem characterAverage_fixes (σ : CompactType K n)
    (f : DerivativeSmoothFunctions K n) (hf : f ∈ compactTypeSubmodule σ) :
    characterAverage ν σ.toContinuousCompactRep f = f := by
  classical
  obtain ⟨s, v, rfl⟩ :=
    (mem_isotypicSpan_iff σ.toContinuousCompactRep f).mp hf
  rw [map_sum]
  exact Finset.sum_congr rfl (fun I _ => characterAverage_intertwiner ν σ I (v I))

end Langlands.Global.ArchimedeanGL.CompactWeightedAverage
