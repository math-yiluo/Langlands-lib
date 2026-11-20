import Langlands.Global.ArchimedeanSmoothFamilyAverage
import Langlands.Global.ArchimedeanSmoothFamilyEnvelopingSpan
import Langlands.Global.ArchimedeanCompactCoefficientAverage

/-! # Compact intertwiners into a closed span of smooth families -/

noncomputable section
universe u w
open MeasureTheory
open scoped Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL.SmoothFamily

open DerivativeSmoothFunctions CompactWeightedAverage

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {ι : Type w}

local notation "V" => SmoothFamily F n ι
local notation "K" => standardInfiniteCompact F n
local notation "ρ" => compactRepresentation (F := F) (n := n) (ι := ι)

variable [MeasurableSpace (standardInfiniteCompact F n)] [BorelSpace (standardInfiniteCompact F n)]
variable (ν : Measure (standardInfiniteCompact F n)) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant]

/-- Average a family against the prescribed inverse matrix coefficient in every slice. -/
def coefficientIntertwiner (τ : ContinuousCompactRep F n) (a : Fin τ.dim) (f : V) :
    τ.toRepresentation.IntertwiningMap ρ :=
  (LinearMap.pi fun i => coefficientAverageLM ν τ a (f i)).intertwiningMap_of_isIntertwiningMap
    _ _ (fun k v => funext fun i => coefficientAverageLM_intertwines ν τ a (f i) k v)

@[simp]
theorem coefficientIntertwiner_apply (τ : ContinuousCompactRep F n) (a : Fin τ.dim) (f : V)
    (v : Fin τ.dim → ℂ) (i : ι) :
    coefficientIntertwiner ν τ a f v i = coefficientAverageLM ν τ a (f i) v := rfl

private theorem coefficientIntertwiner_eq_average (τ : ContinuousCompactRep F n)
    (a : Fin τ.dim) (f : V) (v : Fin τ.dim → ℂ) :
    coefficientIntertwiner ν τ a f v =
      averageLM ⟨Subtype.val, continuous_subtype_val⟩ ν (coefficientWeight τ a v) f := by
  funext i
  apply (toSmooth F n).injective
  apply Subtype.ext
  funext x
  rw [← evalCLM_apply, ← evalCLM_apply, coefficientIntertwiner_apply,
    eval_coefficientAverageLM, averageLM_apply, CompactIndexAverage.eval_averageLM]
  rfl

private theorem continuous_coefficientIntertwiner_apply (τ : ContinuousCompactRep F n)
    (a : Fin τ.dim) (v : Fin τ.dim → ℂ) :
    Continuous (fun f : V => coefficientIntertwiner ν τ a f v) :=
  continuous_pi fun i => (averageCLM ν (coefficientWeight τ a v)).continuous.comp
    (continuous_apply i)

private theorem coefficientIntertwiner_mem_envelopingSpan (τ η : ContinuousCompactRep F n)
    (j : η.toRepresentation.IntertwiningMap ρ) (a : Fin τ.dim) {f : V}
    (hf : f ∈ envelopingSpan j) (v : Fin τ.dim → ℂ) :
    coefficientIntertwiner ν τ a f v ∈ envelopingSpan j := by
  let O := Langlands.FiniteVectors.orbitSpan ρ f
  have : Module.Finite ℂ O := isFiniteVector_of_mem_envelopingSpan j hf
  let r : C(K, InfiniteAdelicGL F n) := ⟨Subtype.val, continuous_subtype_val⟩
  have hO := averageLM_mem_topologicalClosure r ν (coefficientWeight τ a v) O f
    (fun k => O.le_topologicalClosure (Langlands.FiniteVectors.action_mem_orbitSpan ρ k f))
  rw [O.closed_of_finiteDimensional.submodule_topologicalClosure_eq] at hO
  have hle : O ≤ (envelopingSpan j).restrictScalars ℂ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact compactRepresentation_mem_envelopingSpan j k hf
  rw [coefficientIntertwiner_eq_average]
  exact hle hO

private theorem sum_coefficientIntertwiner [IsProbabilityMeasure ν]
    (τ : ContinuousCompactRep F n) (T : τ.toRepresentation.IntertwiningMap ρ)
    (v : Fin τ.dim → ℂ) :
    ∑ a : Fin τ.dim, coefficientIntertwiner ν τ a (T (Pi.single a 1)) v = T v := by
  funext i
  apply (toSmooth F n).injective
  apply Subtype.ext
  funext x
  rw [← evalCLM_apply, ← evalCLM_apply]
  simp only [Finset.sum_apply, map_sum, coefficientIntertwiner_apply, eval_coefficientAverageLM]
  rw [← integral_finsetSum]
  · have heq (k : K) : (∑ a : Fin τ.dim, τ.toRepresentation k⁻¹ v a *
        evalCLM F n (x * k.val) (T (Pi.single a 1) i)) = evalCLM F n x (T v i) := by
      let L := (evalCLM F n (x * k.val)).toLinearMap.comp
        ((LinearMap.proj i).comp T.toLinearMap)
      have hbase : ∑ a : Fin τ.dim, τ.toRepresentation k⁻¹ v a • Pi.single a (1 : ℂ) =
          τ.toRepresentation k⁻¹ v := by
        simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
          Finset.univ_sum_single (τ.toRepresentation k⁻¹ v)
      have h := congrArg L hbase
      simp only [map_sum, map_smul, smul_eq_mul] at h
      have hfixed := Representation.IntertwiningMap.isIntertwining _ _ T k
        (τ.toRepresentation k⁻¹ v)
      rw [Representation.self_inv_apply] at hfixed
      change T v = ρ k (T (τ.toRepresentation k⁻¹ v)) at hfixed
      have hvalue := congrArg (fun f : V => evalCLM F n x (f i)) hfixed
      rw [compactRepresentation_apply, compactAction_apply, evalCLM_rightAction] at hvalue
      exact h.trans hvalue.symm
    simp only [heq, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  · intro a _
    exact (weightedEvaluation (coefficientWeight τ a v)
      (toContinuousMapCLM F n (T (Pi.single a 1) i), x)).continuous
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The common finite-dimensional bound on algebraically generated intertwiners
also bounds the values of intertwiners into the closure of the generated span. -/
theorem exists_finite_cover_of_closure_intertwiner_values [IsProbabilityMeasure ν]
    (τ η : ContinuousCompactRep F n) (j : η.toRepresentation.IntertwiningMap ρ)
    (J : Ideal (EnvelopingCenter F n))
    [Module.Finite ℂ (EnvelopingCenter F n ⧸ J.restrictScalars ℂ)]
    (hJ : ∀ z ∈ J, ∀ v, (z : EnvelopingAlgebra F n) • j v = 0) :
    ∃ E : Submodule ℂ V, Module.Finite ℂ E ∧
      ∀ T : τ.toRepresentation.IntertwiningMap ρ,
        (∀ v, T v ∈ ((envelopingSpan j).restrictScalars ℂ).topologicalClosure) →
        ∀ v, T v ∈ E := by
  obtain ⟨E, hE, hcover⟩ := exists_finite_cover_of_intertwiner_values τ η j J hJ
  refine ⟨E, hE, fun T hT v => ?_⟩
  rw [← sum_coefficientIntertwiner ν τ T v]
  apply Submodule.sum_mem
  intro a _
  have hc : IsClosed ((fun f : V => coefficientIntertwiner ν τ a f v) ⁻¹' (E : Set V)) :=
    E.closed_of_finiteDimensional.preimage (continuous_coefficientIntertwiner_apply ν τ a v)
  have hle : (((envelopingSpan j).restrictScalars ℂ) : Set V) ⊆
      (fun f : V => coefficientIntertwiner ν τ a f v) ⁻¹' (E : Set V) := by
    intro f hf
    exact hcover (coefficientIntertwiner ν τ a f)
      (coefficientIntertwiner_mem_envelopingSpan ν τ η j a hf) v
  exact closure_minimal hle hc (hT _)

end Langlands.Global.ArchimedeanGL.SmoothFamily
