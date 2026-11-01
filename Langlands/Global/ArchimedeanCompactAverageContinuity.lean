import Langlands.Global.ArchimedeanCompactAverageDerivatives

/-! # Continuity of actual weighted compact averaging -/

noncomputable section
universe u
open MeasureTheory Set
open scoped Topology
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL.CompactWeightedAverage

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}
variable [MeasurableSpace (standardInfiniteCompact K n)]
  [BorelSpace (standardInfiniteCompact K n)]
variable (ν : Measure (standardInfiniteCompact K n)) [IsFiniteMeasure ν]

/-- Scalar integration on the Banach space of continuous functions on the
actual compact subgroup. -/
def scalarIntegralCLM : C(standardInfiniteCompact K n, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ k, f k ∂ν
      map_add' := fun f g => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun z f => integral_smul z f }
    (ν.real univ) (fun f => by
      change ‖∫ k, f k ∂ν‖ ≤ ν.real univ * ‖f‖
      simpa only [mul_comm] using
        (norm_integral_le_of_norm_le_const (μ := ν)
          (Filter.Eventually.of_forall fun k => f.norm_coe_le_norm k)))

omit [NumberField K] in
@[simp]
theorem scalarIntegralCLM_apply (f : C(standardInfiniteCompact K n, ℂ)) :
    scalarIntegralCLM ν f = ∫ k, f k ∂ν := rfl

/-- A weighted compact orbit of a continuous function, with the base point
and continuous function as parameters. -/
def weightedEvaluation (w : C(standardInfiniteCompact K n, ℂ))
    (p : C(InfiniteAdelicGL K n, ℂ) × InfiniteAdelicGL K n) :
    C(standardInfiniteCompact K n, ℂ) :=
  ⟨fun k => w k * p.1 (p.2 * k.val),
    w.continuous.mul (p.1.continuous.comp (continuous_const.mul continuous_subtype_val))⟩

omit [MeasurableSpace (standardInfiniteCompact K n)]
  [BorelSpace (standardInfiniteCompact K n)] in
theorem continuous_weightedEvaluation (w : C(standardInfiniteCompact K n, ℂ)) :
    Continuous (weightedEvaluation w) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (w.continuous.comp continuous_snd).mul
    (continuous_eval.comp (continuous_fst.fst.prodMk
      (continuous_fst.snd.mul continuous_snd.subtype_val)))

/-- Scalar compact averaging on continuous functions. -/
def continuousAverage (w : C(standardInfiniteCompact K n, ℂ))
    (f : C(InfiniteAdelicGL K n, ℂ)) : C(InfiniteAdelicGL K n, ℂ) :=
  ⟨fun x => scalarIntegralCLM ν (weightedEvaluation w (f, x)),
    (scalarIntegralCLM ν).continuous.comp
      ((continuous_weightedEvaluation w).comp (continuous_const.prodMk continuous_id))⟩

@[simp]
theorem continuousAverage_apply (w : C(standardInfiniteCompact K n, ℂ))
    (f : C(InfiniteAdelicGL K n, ℂ)) (x : InfiniteAdelicGL K n) :
    continuousAverage ν w f x =
      ∫ k : standardInfiniteCompact K n, w k * f (x * k.val) ∂ν := rfl

theorem continuous_continuousAverage (w : C(standardInfiniteCompact K n, ℂ)) :
    Continuous (continuousAverage ν w) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (scalarIntegralCLM ν).continuous.comp (continuous_weightedEvaluation w)

/-- Weighted compact averaging is a continuous complex linear map for the
compact-open topology on continuous functions. -/
def continuousAverageCLM (w : C(standardInfiniteCompact K n, ℂ)) :
    C(InfiniteAdelicGL K n, ℂ) →L[ℂ] C(InfiniteAdelicGL K n, ℂ) where
  toFun := continuousAverage ν w
  map_add' f g := by
    ext x
    change scalarIntegralCLM ν (weightedEvaluation w (f + g, x)) = _
    have h : weightedEvaluation w (f + g, x) =
        weightedEvaluation w (f, x) + weightedEvaluation w (g, x) := by
      ext k
      exact mul_add _ _ _
    rw [h, map_add]
    rfl
  map_smul' z f := by
    ext x
    change scalarIntegralCLM ν (weightedEvaluation w (z • f, x)) = _
    have h : weightedEvaluation w (z • f, x) = z • weightedEvaluation w (f, x) := by
      ext k
      exact mul_left_comm _ _ _
    rw [h, map_smul]
    rfl
  cont := continuous_continuousAverage ν w

@[simp]
theorem continuousAverageCLM_apply (w : C(standardInfiniteCompact K n, ℂ))
    (f : C(InfiniteAdelicGL K n, ℂ)) (x : InfiniteAdelicGL K n) :
    continuousAverageCLM ν w f x =
      ∫ k : standardInfiniteCompact K n, w k * f (x * k.val) ∂ν := rfl

/-- Every derivative coordinate of the actual average is continuous, by its
finite expansion into scalar compact-open averages. -/
theorem continuous_averageLM (w : C(standardInfiniteCompact K n, ℂ)) :
    Continuous (averageLM ν w) := by
  classical
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro a
  obtain ⟨m, b, c, _, ha⟩ := derivativeExpansion ν a
  have hfun :
      (fun f : DerivativeSmoothFunctions K n =>
        DerivativeSmoothFunctions.derivativeCoordinates K n (averageLM ν w f) a) =
      (fun f => ∑ i, continuousAverageCLM ν (w * c i)
        (DerivativeSmoothFunctions.derivativeCLM K n (b i) f)) := by
    funext f
    ext x
    change (envelopingAction K n a
      (averageSmoothLM ν w (DerivativeSmoothFunctions.toSmooth K n f))).val x = _
    rw [ha]
    simp only [Submodule.coe_sum, Finset.sum_apply, averageSmoothLM_apply, average,
      ContinuousMap.sum_apply, continuousAverageCLM_apply,
      DerivativeSmoothFunctions.derivativeCLM_apply, toContinuousMap]
    rfl
  change Continuous (fun f : DerivativeSmoothFunctions K n =>
    DerivativeSmoothFunctions.derivativeCoordinates K n (averageLM ν w f) a)
  rw [hfun]
  exact continuous_finsetSum _ fun i _ =>
    (continuousAverageCLM ν (w * c i)).continuous.comp
      (DerivativeSmoothFunctions.derivativeCLM K n (b i)).continuous

/-- The actual smooth weighted compact average, continuous in the full
enveloping derivative topology. -/
def averageCLM (w : C(standardInfiniteCompact K n, ℂ)) :
    DerivativeSmoothFunctions K n →L[ℂ] DerivativeSmoothFunctions K n :=
  ⟨averageLM ν w, continuous_averageLM ν w⟩

@[simp]
theorem eval_averageCLM (w : C(standardInfiniteCompact K n, ℂ))
    (f : DerivativeSmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    DerivativeSmoothFunctions.evalCLM K n x (averageCLM ν w f) =
      ∫ k : standardInfiniteCompact K n,
        w k * DerivativeSmoothFunctions.evalCLM K n (x * k.val) f ∂ν :=
  eval_averageLM ν w f x

end Langlands.Global.ArchimedeanGL.CompactWeightedAverage
