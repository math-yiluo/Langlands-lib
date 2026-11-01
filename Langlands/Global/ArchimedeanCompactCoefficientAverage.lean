import Langlands.Global.ArchimedeanCompactAverageOrbitClosure
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.LinearAlgebra.Matrix.Trace

/-! # Matrix-coefficient averages for the actual compact action -/

noncomputable section
universe u
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL.CompactWeightedAverage

open DerivativeSmoothFunctions

variable {K : Type u} [Field K] [NumberField K] {n : ℕ}

private theorem ext_eval {f g : DerivativeSmoothFunctions K n}
    (h : ∀ x, evalCLM K n x f = evalCLM K n x g) : f = g := by
  apply (toSmooth K n).injective
  apply Subtype.ext
  funext x
  simpa only [evalCLM_apply] using h x

variable [MeasurableSpace (standardInfiniteCompact K n)]
  [BorelSpace (standardInfiniteCompact K n)]
variable (ν : Measure (standardInfiniteCompact K n)) [IsFiniteMeasure ν]

private theorem integrable_weighted (w : C(standardInfiniteCompact K n, ℂ))
    (f : DerivativeSmoothFunctions K n) (x : InfiniteAdelicGL K n) :
    Integrable (fun k : standardInfiniteCompact K n =>
      w k * evalCLM K n (x * k.val) f) ν :=
  (weightedEvaluation w (toContinuousMapCLM K n f, x)).continuous
    |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- For fixed input, the actual average is complex linear in its weight. -/
def weightAverageLM (f : DerivativeSmoothFunctions K n) :
    C(standardInfiniteCompact K n, ℂ) →ₗ[ℂ] DerivativeSmoothFunctions K n where
  toFun w := averageCLM ν w f
  map_add' w z := by
    apply ext_eval
    intro x
    simp only [eval_averageCLM, map_add, ContinuousMap.add_apply, add_mul]
    exact integral_add (integrable_weighted ν w f x) (integrable_weighted ν z f x)
  map_smul' c w := by
    apply ext_eval
    intro x
    simp only [eval_averageCLM, map_smul, ContinuousMap.smul_apply, smul_eq_mul]
    simpa only [mul_assoc, RingHom.id_apply] using
      (integral_const_mul c (fun k : standardInfiniteCompact K n =>
        w k * evalCLM K n (x * k.val) f) (μ := ν))

/-- A matrix coefficient of the inverse source representation, as a continuous weight. -/
def coefficientWeight (τ : ContinuousCompactRep K n) (j : Fin τ.dim)
    (v : Fin τ.dim → ℂ) : C(standardInfiniteCompact K n, ℂ) :=
  ⟨fun k => τ.toRepresentation k⁻¹ v j,
    (continuous_apply j).comp ((τ.continuous_orbit v).comp continuous_inv)⟩

/-- The inverse matrix coefficient is complex linear in the source vector. -/
def coefficientWeightLM (τ : ContinuousCompactRep K n) (j : Fin τ.dim) :
    (Fin τ.dim → ℂ) →ₗ[ℂ] C(standardInfiniteCompact K n, ℂ) where
  toFun := coefficientWeight τ j
  map_add' v z := by ext k; simp [coefficientWeight]
  map_smul' c v := by ext k; simp [coefficientWeight]

/-- A matrix-coefficient average, linear in its source vector. -/
def coefficientAverageLM (τ : ContinuousCompactRep K n) (j : Fin τ.dim)
    (f : DerivativeSmoothFunctions K n) :
    (Fin τ.dim → ℂ) →ₗ[ℂ] DerivativeSmoothFunctions K n :=
  (weightAverageLM ν f).comp (coefficientWeightLM τ j)

@[simp]
theorem eval_coefficientAverageLM (τ : ContinuousCompactRep K n) (j : Fin τ.dim)
    (f : DerivativeSmoothFunctions K n) (v : Fin τ.dim → ℂ)
    (x : InfiniteAdelicGL K n) :
    evalCLM K n x (coefficientAverageLM ν τ j f v) =
      ∫ k : standardInfiniteCompact K n,
        τ.toRepresentation k⁻¹ v j * evalCLM K n (x * k.val) f ∂ν :=
  eval_averageCLM ν (coefficientWeight τ j v) f x

/-- Left invariance makes each actual matrix-coefficient average an intertwiner. -/
theorem coefficientAverageLM_intertwines [ν.IsMulLeftInvariant]
    (τ : ContinuousCompactRep K n) (j : Fin τ.dim)
    (f : DerivativeSmoothFunctions K n)
    (h : standardInfiniteCompact K n) (v : Fin τ.dim → ℂ) :
    coefficientAverageLM ν τ j f (τ.toRepresentation h v) =
      compactAction K n h (coefficientAverageLM ν τ j f v) := by
  apply ext_eval
  intro x
  rw [eval_coefficientAverageLM]
  rw [compactAction_apply, evalCLM_rightAction]
  rw [eval_coefficientAverageLM]
  have hi := integral_mul_left_eq_self (μ := ν)
    (fun k : standardInfiniteCompact K n =>
      τ.toRepresentation k⁻¹ (τ.toRepresentation h v) j *
        evalCLM K n (x * k.val) f) h
  rw [← hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro k
  simp only [mul_inv_rev, map_mul, Module.End.mul_apply, Representation.inv_self_apply,
    Subgroup.coe_mul, mul_assoc]

/-- The matrix-coefficient average as an actual algebraic intertwining map. -/
def coefficientIntertwiner [ν.IsMulLeftInvariant]
    (τ : ContinuousCompactRep K n) (j : Fin τ.dim)
    (f : DerivativeSmoothFunctions K n) :
    τ.toRepresentation.IntertwiningMap (compactAction K n) :=
  (coefficientAverageLM ν τ j f).intertwiningMap_of_isIntertwiningMap
    τ.toRepresentation (compactAction K n)
    (coefficientAverageLM_intertwines ν τ j f)

/-- Every matrix-coefficient average lies in the published algebraic isotypic span. -/
theorem coefficientAverageLM_mem [ν.IsMulLeftInvariant]
    (τ : ContinuousCompactRep K n) (j : Fin τ.dim)
    (f : DerivativeSmoothFunctions K n) (v : Fin τ.dim → ℂ) :
    coefficientAverageLM ν τ j f v ∈ isotypicSpan τ :=
  range_le_isotypicSpan τ (coefficientIntertwiner ν τ j f) ⟨v, rfl⟩

/-- The degree times inverse character, expressed as the finite diagonal sum. -/
def characterWeight (τ : ContinuousCompactRep K n) : C(standardInfiniteCompact K n, ℂ) :=
  (τ.dim : ℂ) • ∑ j : Fin τ.dim, coefficientWeight τ j (Pi.single j 1)

/-- The actual continuous operator given by the degree times inverse character. -/
def characterAverage (τ : ContinuousCompactRep K n) :
    DerivativeSmoothFunctions K n →L[ℂ] DerivativeSmoothFunctions K n :=
  averageCLM ν (characterWeight τ)

omit [NumberField K] [MeasurableSpace (standardInfiniteCompact K n)]
  [BorelSpace (standardInfiniteCompact K n)] in
theorem characterWeight_apply (τ : ContinuousCompactRep K n)
    (k : standardInfiniteCompact K n) :
    characterWeight τ k =
      (τ.dim : ℂ) * Matrix.trace (LinearMap.toMatrix' (τ.toRepresentation k⁻¹)) := by
  simp [characterWeight, coefficientWeight, Matrix.trace, LinearMap.toMatrix'_apply]

omit [NumberField K] [MeasurableSpace (standardInfiniteCompact K n)]
  [BorelSpace (standardInfiniteCompact K n)] in
/-- Cyclic invariance of trace gives the centrality needed for compact equivariance. -/
theorem characterWeight_mul_comm (τ : ContinuousCompactRep K n)
    (h k : standardInfiniteCompact K n) :
    characterWeight τ (h * k) = characterWeight τ (k * h) := by
  simp only [characterWeight_apply, mul_inv_rev, map_mul, LinearMap.toMatrix'_mul]
  rw [Matrix.trace_mul_comm]

/-- The character average is a finite sum of values of actual intertwiners. -/
theorem characterAverage_eq (τ : ContinuousCompactRep K n)
    (f : DerivativeSmoothFunctions K n) :
    characterAverage ν τ f =
      (τ.dim : ℂ) • ∑ j : Fin τ.dim,
        coefficientAverageLM ν τ j f (Pi.single j 1) := by
  change weightAverageLM ν f
    ((τ.dim : ℂ) • ∑ j : Fin τ.dim, coefficientWeight τ j (Pi.single j 1)) = _
  rw [map_smul, map_sum]
  rfl

/-- Inverse-character averaging has algebraic isotypic range, without closing it. -/
theorem characterAverage_mem [ν.IsMulLeftInvariant]
    (τ : ContinuousCompactRep K n) (f : DerivativeSmoothFunctions K n) :
    characterAverage ν τ f ∈ isotypicSpan τ := by
  rw [characterAverage_eq]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ =>
    coefficientAverageLM_mem ν τ j f _)

/-- Bi-invariance and the cyclic inverse character make the actual average equivariant. -/
theorem characterAverage_compactAction [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
    (τ : ContinuousCompactRep K n) (h : standardInfiniteCompact K n)
    (f : DerivativeSmoothFunctions K n) :
    characterAverage ν τ (compactAction K n h f) =
      compactAction K n h (characterAverage ν τ f) := by
  apply ext_eval
  intro x
  simp only [characterAverage, eval_averageCLM, compactAction_apply, evalCLM_rightAction]
  have hi := integral_mul_left_eq_self (μ := ν)
    (fun k : standardInfiniteCompact K n =>
      characterWeight τ k * evalCLM K n ((x * k.val) * h.val) f) h
  have hj := integral_mul_right_eq_self (μ := ν)
    (fun k : standardInfiniteCompact K n =>
      characterWeight τ k * evalCLM K n ((x * h.val) * k.val) f) h
  rw [← hi, ← hj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro k
  dsimp only
  rw [characterWeight_mul_comm τ h k]
  simp only [Subgroup.coe_mul, mul_assoc]

/-- The character average retains the actual closed compact-orbit containment. -/
theorem characterAverage_mem_closed_compactOrbit
    (τ : ContinuousCompactRep K n) (f : DerivativeSmoothFunctions K n) :
    characterAverage ν τ f ∈
      (Submodule.span ℂ (Set.range fun k : standardInfiniteCompact K n =>
        compactAction K n k f)).topologicalClosure :=
  average_mem_closed_compactOrbit ν (characterWeight τ) f

end Langlands.Global.ArchimedeanGL.CompactWeightedAverage
