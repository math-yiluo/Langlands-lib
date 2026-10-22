import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Descent of a positive integral through an averaging map

This algebraic construction isolates the final functional step in quotient
integration. Surjectivity, positive lifting and kernel vanishing remain explicit
inputs to this helper and must be proved for the actual averaging map.
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory CompactlySupportedContinuousMap
open scoped CompactlySupported

section Algebra

variable {A B : Type*}
variable [AddCommGroup A] [PartialOrder A] [Module ℝ A]
variable [AddCommGroup B] [PartialOrder B] [IsOrderedAddMonoid B] [Module ℝ B]
variable (P : A →ₗ[ℝ] B) (hP : Function.Surjective P)
variable (I : A →ₚ[ℝ] ℝ) (hker : P.ker ≤ I.toLinearMap.ker)
variable (hpos : ∀ b : B, 0 ≤ b → ∃ a : A, 0 ≤ a ∧ P a = b)

/-- The functional induced on the target of a surjective averaging map.
Its well-definedness is kernel containment; its positivity uses positive lifts. -/
def descendPositiveLinearMap : B →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    ((P.ker.liftQ I.toLinearMap hker).comp
      (P.quotKerEquivOfSurjective hP).symm.toLinearMap) (by
        intro b hb
        obtain ⟨a, ha, rfl⟩ := hpos b hb
        simpa using I.map_nonneg ha)

@[simp] theorem descendPositiveLinearMap_apply (a : A) :
    descendPositiveLinearMap P hP I hker hpos (P a) = I a := by
  change (P.ker.liftQ I.toLinearMap hker)
    ((P.quotKerEquivOfSurjective hP).symm (P a)) = I a
  simp

/-- The descended functional is uniquely determined by its values on averages. -/
theorem descendPositiveLinearMap_unique (J : B →ₚ[ℝ] ℝ)
    (hJ : ∀ a : A, J (P a) = I a) :
    J = descendPositiveLinearMap P hP I hker hpos := by
  ext b
  obtain ⟨a, rfl⟩ := hP b
  rw [descendPositiveLinearMap_apply, hJ]

end Algebra

section Measure

variable {X Y : Type*}
variable [TopologicalSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
variable [MeasurableSpace Y] [BorelSpace Y]
variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
variable (P : C_c(X, ℝ) →ₗ[ℝ] C_c(Y, ℝ)) (hP : Function.Surjective P)
variable (hker : P.ker ≤ (integralPositiveLinearMap μ).toLinearMap.ker)
variable (hpos : ∀ φ : C_c(Y, ℝ), 0 ≤ φ → ∃ f : C_c(X, ℝ), 0 ≤ f ∧ P f = φ)

/-- A regular measure constructed from actual ambient integration and a
surjective averaging map with positive lifts and the required kernel property. -/
def measureOfPositiveAveraging : Measure Y :=
  RealRMK.rieszMeasure
    (descendPositiveLinearMap P hP (integralPositiveLinearMap μ) hker hpos)

instance measureOfPositiveAveraging_regular :
    (measureOfPositiveAveraging μ P hP hker hpos).Regular := by
  unfold measureOfPositiveAveraging
  infer_instance

/-- The constructed measure integrates averages by the supplied ambient integral. -/
theorem integral_measureOfPositiveAveraging (f : C_c(X, ℝ)) :
    (∫ y, P f y ∂measureOfPositiveAveraging μ P hP hker hpos) = ∫ x, f x ∂μ := by
  rw [measureOfPositiveAveraging, RealRMK.integral_rieszMeasure,
    descendPositiveLinearMap_apply]
  rfl

/-- One nonzero ambient test integral suffices to make the constructed measure
nonzero. The existence of such a test is a separate input at this level. -/
theorem measureOfPositiveAveraging_ne_zero
    (hμ : ∃ f : C_c(X, ℝ), (∫ x, f x ∂μ) ≠ 0) :
    measureOfPositiveAveraging μ P hP hker hpos ≠ 0 := by
  intro hzero
  obtain ⟨f, hf⟩ := hμ
  have h := integral_measureOfPositiveAveraging μ P hP hker hpos f
  rw [hzero, integral_zero_measure] at h
  exact hf h.symm

/-- The integration formula on averages determines the regular measure uniquely. -/
theorem measureOfPositiveAveraging_unique (ν : Measure Y) [ν.Regular]
    (hν : ∀ f : C_c(X, ℝ), (∫ y, P f y ∂ν) = ∫ x, f x ∂μ) :
    ν = measureOfPositiveAveraging μ P hP hker hpos := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro φ
  obtain ⟨f, rfl⟩ := hP φ
  rw [hν, integral_measureOfPositiveAveraging]

/-- An equivariant averaging map transfers integral invariance to invariance
of the constructed measure under a homeomorphism of its target. -/
theorem measureOfPositiveAveraging_preserving (e : Y ≃ₜ Y)
    (T : C_c(X, ℝ) → C_c(X, ℝ))
    (hPT : ∀ f : C_c(X, ℝ), ∀ y, P (T f) y = P f (e y))
    (hT : ∀ f : C_c(X, ℝ), (∫ x, T f x ∂μ) = ∫ x, f x ∂μ) :
    MeasurePreserving e (measureOfPositiveAveraging μ P hP hker hpos)
      (measureOfPositiveAveraging μ P hP hker hpos) := by
  let ν := measureOfPositiveAveraging μ P hP hker hpos
  have : ν.Regular := measureOfPositiveAveraging_regular μ P hP hker hpos
  have : (Measure.map e ν).Regular := Measure.Regular.map e
  refine ⟨e.continuous.measurable, ?_⟩
  apply measureOfPositiveAveraging_unique μ P hP hker hpos
  intro f
  change (∫ y, P f y ∂Measure.map e.toMeasurableEquiv ν) = ∫ x, f x ∂μ
  rw [integral_map_equiv e.toMeasurableEquiv]
  change (∫ y, P f (e y) ∂ν) = ∫ x, f x ∂μ
  simp_rw [← hPT]
  rw [integral_measureOfPositiveAveraging, hT]

end Measure

end Langlands.QuotientIntegration
