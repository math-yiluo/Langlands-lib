import Langlands.Global.ArchimedeanSmoothActionContinuityStatement
import Langlands.Global.ArchimedeanCovarianceProof
import Langlands.Global.ArchimedeanAdjointCoefficientsProof
import Langlands.Global.ArchimedeanConvolution

noncomputable section
universe u
open scoped Topology
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

private theorem derivative_rightAction_of_covariance
    (g : InfiniteAdelicGL K n) (a : EnvelopingAlgebra K n) (f : SmoothFunctions K n) :
    envelopingAction K n a (smoothRightAction K n g f) =
      smoothRightAction K n g (envelopingAction K n (envelopingConjugation K n g⁻¹ a) f) := by
  have h := envelopingRightCovariance K n g (envelopingConjugation K n g⁻¹ a) f
  rw [envelopingConjugation_inv, AlgEquiv.apply_symm_apply] at h
  exact h.symm

private theorem envelopingAction_sum_smul_apply (m : ℕ)
    (b : Fin m → EnvelopingAlgebra K n) (c : Fin m → ℂ)
    (f : SmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    (envelopingAction K n (∑ i, c i • b i) f).val x =
      ∑ i, c i * (envelopingAction K n (b i) f).val x := by
  simp [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply]

/-- The actual right regular action is jointly continuous for the derivative topology. -/
theorem smoothRightActionContinuity :
    SmoothRightActionContinuityStatement K n := by
  unfold SmoothRightActionContinuityStatement
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  obtain ⟨m, b, c, hc⟩ := envelopingConjugationCoefficients K n a
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun q :
    (InfiniteAdelicGL K n × DerivativeSmoothFunctions K n) × InfiniteAdelicGL K n =>
    (envelopingAction K n a
      (smoothRightAction K n q.1.1 (DerivativeSmoothFunctions.toSmooth K n q.1.2))).val q.2)
  simp_rw [derivative_rightAction_of_covariance K n, smoothRightAction_apply,
    hc, envelopingAction_sum_smul_apply]
  apply continuous_finsetSum
  intro i hi
  apply Continuous.mul
  · exact (c i).continuous.comp continuous_fst.fst.inv
  · exact continuous_eval.comp
      (((DerivativeSmoothFunctions.derivativeCLM K n (b i)).continuous.comp
        continuous_fst.snd).prodMk (continuous_snd.mul continuous_fst.fst))

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    SmoothRightActionContinuityStatement K n :=
  @smoothRightActionContinuity

end Langlands.Global.ArchimedeanGL
