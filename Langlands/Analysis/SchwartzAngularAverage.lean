import Langlands.Analysis.SchwartzLinearAverage
import Langlands.Analysis.SchwartzPositiveMellin
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! # Angular averages of Schwartz tests in complex coordinates -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis

variable {ι : Type*} [Fintype ι]

local notation "R" => ι → ℝ
local notation "Z" => ι → ℂ

private abbrev angularLineMeasure : Measure ℝ :=
  volume.restrict (Ioo (-Real.pi) Real.pi)

private instance angularLineMeasure_finite : IsFiniteMeasure angularLineMeasure :=
  ⟨by simp [Real.volume_Ioo]⟩

/-- Product Lebesgue measure on the angular coordinate intervals. -/
def angularCoordinateMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => angularLineMeasure)

instance angularCoordinateMeasure_finite : IsFiniteMeasure (angularCoordinateMeasure ι) :=
  inferInstanceAs (IsFiniteMeasure (Measure.pi (fun _ : ι => angularLineMeasure)))

/-- Group the finite family of polar radii and angles into Cartesian pairs. -/
abbrev pairPolarCoordinates : ((ι → ℝ) × (ι → ℝ)) ≃ᵐ (ι → ℝ × ℝ) :=
  (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι).symm

omit [Fintype ι] in
theorem pairPolarCoordinates_apply (r θ : R) (i : ι) :
    pairPolarCoordinates (r, θ) i = (r i, θ i) := rfl

/-- Separating the polar coordinate restrictions gives the product of
the radial and angular measures. -/
theorem measurePreserving_pairPolarCoordinates :
    MeasurePreserving (pairPolarCoordinates (ι := ι))
      ((positiveCoordinateMeasure ι).prod (angularCoordinateMeasure ι))
      (volume.restrict (univ.pi fun _ : ι => Complex.polarCoord.target)) := by
  rw [volume_pi, Measure.restrict_pi_pi]
  have hρ : (volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target =
      positiveLineMeasure.prod angularLineMeasure :=
    (Measure.prod_restrict (Ioi (0 : ℝ)) (Ioo (-Real.pi) Real.pi)).symm
  simp_rw [hρ]
  exact ((measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι
    (fun _ => positiveLineMeasure) (fun _ => angularLineMeasure)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι))

/-- The polar angle as a unit complex phase. -/
def complexAngularPhase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem norm_complexAngularPhase (θ : ℝ) : ‖complexAngularPhase θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- The polar angle weight for integral angular exponents. -/
def complexAngularWeight (m : ι → ℤ) (θ : R) : ℂ :=
  ∏ i, complexAngularPhase (m i * θ i)

theorem norm_complexAngularWeight (m : ι → ℤ) (θ : R) : ‖complexAngularWeight m θ‖ = 1 := by
  simp [complexAngularWeight, norm_complexAngularPhase]

theorem continuous_complexAngularWeight (m : ι → ℤ) :
    Continuous (complexAngularWeight m) := by
  unfold complexAngularWeight complexAngularPhase
  fun_prop

private def realCoordinateInclusion : R →L[ℝ] Z :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

private def angularRotation (θ : R) : R →L[ℝ] Z :=
  (ContinuousLinearMap.mul ℝ Z (fun i => complexAngularPhase (θ i))).comp realCoordinateInclusion

private theorem continuous_angularRotation : Continuous (angularRotation (ι := ι)) := by
  have hPhase : Continuous (fun θ : R => fun i => complexAngularPhase (θ i)) := by
    unfold complexAngularPhase
    fun_prop
  exact ((ContinuousLinearMap.compL ℝ R Z Z).flip realCoordinateInclusion).continuous.comp
    ((ContinuousLinearMap.mul ℝ Z).continuous.comp hPhase)

private theorem angularRotation_apply (θ r : R) (i : ι) :
    angularRotation θ r i = complexAngularPhase (θ i) * (r i : ℂ) := rfl

private theorem norm_angularRotation (θ r : R) : ‖angularRotation θ r‖ = ‖r‖ := by
  have hi (i : ι) : ‖angularRotation θ r i‖ = ‖r i‖ := by
    rw [angularRotation_apply, norm_mul, norm_complexAngularPhase, one_mul, Complex.norm_real]
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
      (hi i).trans_le (norm_le_pi_norm r i)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i =>
      (hi i).symm.trans_le (norm_le_pi_norm (angularRotation θ r) i)

private theorem integrable_complexAngularWeight (m : ι → ℤ) :
    Integrable (complexAngularWeight m) (angularCoordinateMeasure ι) :=
  (integrable_const (1 : ℝ)).mono'
    (continuous_complexAngularWeight m).aestronglyMeasurable
    (Eventually.of_forall fun θ => (norm_complexAngularWeight m θ).le)

/-- Integrate a complex Schwartz test over the angular variables with character weight.
The remaining function of the real radii is Schwartz. -/
def schwartzAngularAverage (m : ι → ℤ) (Φ : SchwartzMap Z ℂ) : SchwartzMap R ℂ :=
  schwartzLinearAverage (angularCoordinateMeasure ι) (complexAngularWeight m)
    (integrable_complexAngularWeight m) angularRotation continuous_angularRotation
    (fun θ => (angularRotation θ).opNorm_le_bound zero_le_one fun r => by
      rw [norm_angularRotation, one_mul])
    zero_le_one (fun θ r => by rw [norm_angularRotation, one_mul]) Φ

theorem schwartzAngularAverage_apply (m : ι → ℤ) (Φ : SchwartzMap Z ℂ) (r : R) :
    schwartzAngularAverage m Φ r =
      ∫ θ, complexAngularWeight m θ * Φ (fun i => complexAngularPhase (θ i) * (r i : ℂ))
        ∂angularCoordinateMeasure ι := rfl

end Langlands.Analysis
