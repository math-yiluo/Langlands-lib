import Langlands.Representation.Unitary.IntegratedOperator
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral

/-! # Probability Haar averaging of a continuous isometric action -/

noncomputable section

namespace Langlands.Analysis

open MeasureTheory TopologicalSpace

universe uK uE uD

variable (K : Type uK) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

/-- Haar measure on the actual compact group, normalized on its whole carrier. -/
def compactProbabilityHaar : Measure K :=
  Measure.haarMeasure (⊤ : PositiveCompacts K)

instance compactProbabilityHaar_isHaarMeasure : (compactProbabilityHaar K).IsHaarMeasure :=
  inferInstanceAs (Measure.haarMeasure (⊤ : PositiveCompacts K)).IsHaarMeasure

instance compactProbabilityHaar_regular : (compactProbabilityHaar K).Regular :=
  inferInstanceAs (Measure.haarMeasure (⊤ : PositiveCompacts K)).Regular

instance compactProbabilityHaar_isProbabilityMeasure :
    IsProbabilityMeasure (compactProbabilityHaar K) where
  measure_univ := by
    change Measure.haarMeasure (⊤ : PositiveCompacts K) Set.univ = 1
    simpa only [PositiveCompacts.coe_top] using
      (Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts K)))

variable [SecondCountableTopology K]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  (π : K →* (E →L[ℂ] E))
  (hnorm : ∀ (k : K) (x : E), ‖π k x‖ = ‖x‖)
  (hcont : ∀ x : E, Continuous (fun k => π k x))

local notation "μ" => compactProbabilityHaar K

include hcont in
omit [CompleteSpace E] in
/-- Continuous orbits of the supplied original action are strongly measurable. -/
theorem compactIsometricOrbit_aestronglyMeasurable (x : E) :
    AEStronglyMeasurable (fun k => π k x) μ :=
  (hcont x).stronglyMeasurable.aestronglyMeasurable

include hnorm hcont in
omit [CompleteSpace E] in
/-- The unweighted orbit has an absolutely convergent Bochner integral. -/
theorem compactIsometricOrbit_integrable (x : E) :
    Integrable (fun k => π k x) μ := by
  simpa only [one_smul] using
    (isometricActionIntegrand_integrable μ π hnorm
      (compactIsometricOrbit_aestronglyMeasurable K π hcont)
      (fun _ => (1 : ℂ)) (integrable_const _) x)

/-- The actual probability Haar integral, as a bounded complex-linear operator. -/
def compactIsometricAverage : E →L[ℂ] E :=
  integratedIsometricAction μ π hnorm
    (compactIsometricOrbit_aestronglyMeasurable K π hcont)
    (fun _ => (1 : ℂ)) (integrable_const _)

@[simp]
theorem compactIsometricAverage_apply (x : E) :
    compactIsometricAverage K π hnorm hcont x = ∫ k, π k x ∂μ := by
  simp only [compactIsometricAverage, integratedIsometricAction_apply, one_smul]

/-- The normalization makes the constructed average a contraction. -/
theorem norm_compactIsometricAverage_le :
    ‖compactIsometricAverage K π hnorm hcont‖ ≤ 1 := by
  simpa only [compactIsometricAverage, norm_one, integral_const, probReal_univ, one_smul] using
    (integratedIsometricAction_norm_le μ π hnorm
      (compactIsometricOrbit_aestronglyMeasurable K π hcont)
      (fun _ => (1 : ℂ)) (integrable_const _))

/-- Every value of the average is fixed by the original action. -/
theorem compactIsometricAverage_fixed (k : K) (x : E) :
    π k (compactIsometricAverage K π hnorm hcont x) =
      compactIsometricAverage K π hnorm hcont x := by
  simp only [compactIsometricAverage_apply]
  rw [← (π k).integral_comp_comm (compactIsometricOrbit_integrable K π hnorm hcont x)]
  have hm : (fun l => π k (π l x)) = fun l => π (k * l) x := by
    funext l
    exact congrArg (fun A : E →L[ℂ] E => A x) (π.map_mul k l).symm
  rw [hm]
  exact integral_mul_left_eq_self (fun l => π l x) k

/-- The average retracts every vector fixed by the supplied action. -/
theorem compactIsometricAverage_eq_self (x : E) (hx : ∀ k : K, π k x = x) :
    compactIsometricAverage K π hnorm hcont x = x := by
  rw [compactIsometricAverage_apply]
  simp only [hx, integral_const, probReal_univ, one_smul]

/-- Its fixed set is exactly the original action's fixed-vector set. -/
theorem compactIsometricAverage_eq_self_iff (x : E) :
    compactIsometricAverage K π hnorm hcont x = x ↔ ∀ k : K, π k x = x := by
  constructor
  · intro hx k
    rw [← hx]
    exact compactIsometricAverage_fixed K π hnorm hcont k x
  · exact compactIsometricAverage_eq_self K π hnorm hcont x

/-- Averaging twice is literally the same bounded operator. -/
theorem compactIsometricAverage_idempotent :
    (compactIsometricAverage K π hnorm hcont).comp
      (compactIsometricAverage K π hnorm hcont) =
        compactIsometricAverage K π hnorm hcont := by
  apply ContinuousLinearMap.ext
  intro x
  exact compactIsometricAverage_eq_self K π hnorm hcont _
    (fun k => compactIsometricAverage_fixed K π hnorm hcont k x)

variable {D : Type uD} [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  (σ : K →* (D →L[ℂ] D))
  (hσnorm : ∀ (k : K) (x : D), ‖σ k x‖ = ‖x‖)
  (hσcont : ∀ x : D, Continuous (fun k => σ k x))

/-- Every original continuous linear intertwiner commutes with the constructed averages. -/
theorem compactIsometricAverage_intertwiner (U : E →L[ℂ] D)
    (hU : ∀ (k : K) (x : E), U (π k x) = σ k (U x)) (x : E) :
    U (compactIsometricAverage K π hnorm hcont x) =
      compactIsometricAverage K σ hσnorm hσcont (U x) := by
  rw [compactIsometricAverage_apply, compactIsometricAverage_apply,
    ← U.integral_comp_comm (compactIsometricOrbit_integrable K π hnorm hcont x)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun k => hU k x))

end Langlands.Analysis
