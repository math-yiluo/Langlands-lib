import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity
import Langlands.Representation.RankinSelberg.RankOneQuotient
import Langlands.Analysis.Local.QuotientAveragingKernel
import Langlands.Analysis.Local.QuotientFunctional
import Langlands.Analysis.Local.QuotientComplex
import Langlands.Analysis.Local.QuotientTranslation

/-!
# The normalized unipotent quotient measure in every rank

The real averaging map and ambient Haar integral define a positive functional
on compactly supported quotient functions. Its Riesz measure satisfies the
published complex Weil formula and agrees with the rank-one construction.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory MeasureTheory.Measure QuotientIntegration
open scoped CompactlySupported

universe uF

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem quotient_localField_t2 : T2Space F := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  have := isUniformAddGroup_of_addCommGroup (G := F)
  infer_instance

attribute [local instance] quotient_localField_t2

private instance quotient_matrix_locallyCompact (n : ℕ) :
    LocallyCompactSpace (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin (n + 1) → Fin (n + 1) → F))

private instance unipotentQuotient_t2 (n : ℕ) :
    T2Space (LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F)) :=
  leftQuotient_t2Space _ (GeneralLinear.UpperUnipotent.isClosed (R := F))

private instance unipotentQuotient_locallyCompact (n : ℕ) :
    LocallyCompactSpace (LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F)) :=
  leftQuotient_locallyCompactSpace _

variable (n : ℕ)
variable [MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) F)]
  [BorelSpace (GeneralLinear.upperUnipotent (n + 1) F)]

private abbrev unipotentAverage :=
  quotientAverageRealLinear (GeneralLinear.upperUnipotent (n + 1) F)
    (GeneralLinear.UpperUnipotent.isClosed (R := F)) (unipotentHaar F n)

private theorem unipotentAverage_lift
    (φ : C_c(LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F), ℝ)) :
    ∃ f : C_c(Matrix.GeneralLinearGroup (Fin (n + 1)) F, ℝ),
      unipotentAverage F n f = φ ∧ (0 ≤ φ → 0 ≤ f) := by
  obtain ⟨f, hf, hp⟩ := realQuotientPositiveLifting
    (GeneralLinear.upperUnipotent (n + 1) F)
    (GeneralLinear.UpperUnipotent.isClosed (R := F)) (unipotentHaar F n) φ
  refine ⟨f, ?_, hp⟩
  ext q
  induction q using Quotient.inductionOn with
  | h g => exact hf g

private theorem unipotentAverage_surjective :
    Function.Surjective (unipotentAverage F n) := by
  intro φ
  obtain ⟨f, hf, _⟩ := unipotentAverage_lift F n φ
  exact ⟨f, hf⟩

private theorem unipotentAverage_positive :
    ∀ φ, 0 ≤ φ → ∃ f, 0 ≤ f ∧ unipotentAverage F n f = φ := by
  intro φ hφ
  obtain ⟨f, hf, hp⟩ := unipotentAverage_lift F n φ
  exact ⟨f, hp hφ, hf⟩

variable [MeasurableSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]
  [BorelSpace (Matrix.GeneralLinearGroup (Fin (n + 1)) F)]

private theorem unipotentAverage_kernel :
    (unipotentAverage F n).ker ≤
      (CompactlySupportedContinuousMap.integralPositiveLinearMap
        (generalLinearHaar F n)).toLinearMap.ker := by
  intro f hf
  change (∫ g, f g ∂generalLinearHaar F n) = 0
  apply realAveragingKernelIntegralZero (GeneralLinear.upperUnipotent (n + 1) F)
    (GeneralLinear.UpperUnipotent.isClosed (R := F))
    (generalLinearHaar F n) (unipotentHaar F n) f
  intro g
  exact congrArg (fun φ => φ (Quotient.mk _ g)) (LinearMap.mem_ker.mp hf)

variable [MeasurableSpace (LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F))]
  [BorelSpace (LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F))]

/-- The Riesz measure of the positive quotient functional defined by actual
normalized ambient integration and actual unipotent averaging. -/
def unipotentQuotientHaar :
    Measure (LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F)) :=
  measureOfPositiveAveraging (generalLinearHaar F n) (unipotentAverage F n)
    (unipotentAverage_surjective F n) (unipotentAverage_kernel F n)
    (unipotentAverage_positive F n)

instance unipotentQuotientHaar_regular : (unipotentQuotientHaar F n).Regular :=
  measureOfPositiveAveraging_regular _ _ _ _ _

/-- The real Weil integration formula used to construct the measure. -/
theorem integral_unipotentQuotientHaar_real
    (f : C_c(Matrix.GeneralLinearGroup (Fin (n + 1)) F, ℝ)) :
    (∫ q, quotientAverageReal (GeneralLinear.upperUnipotent (n + 1) F)
      (unipotentHaar F n) f q ∂unipotentQuotientHaar F n) =
        ∫ g, f g ∂generalLinearHaar F n :=
  integral_measureOfPositiveAveraging _ _ _ _ _ f

/-- All five compatibility fields, including the exact complex Weil formula. -/
theorem unipotentQuotientHaar_isCompatible :
    IsCompatible (GeneralLinear.upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) (unipotentQuotientHaar F n) where
  nonzero := by
    apply measureOfPositiveAveraging_ne_zero
    apply exists_compact_integral_ne_zero
    intro hz
    have hm := generalLinearHaar_integralSubgroup F n
    rw [hz] at hm
    simp at hm
  regular := inferInstance
  right_invariant g := by
    apply measureOfPositiveAveraging_preserving _ _ _ _ _
      (rightTranslate _ g) (compactRightTranslate g)
    · exact compactAveraging_rightTranslate _ _ _ (fun _ _ => rfl) g
    · exact integral_compactRightTranslate _ g
  averaging_integrable f hf hc := by
    apply quotientAverage_integrable_of_real _ _ (unipotentAverage F n) (fun _ _ => rfl)
      _ f hf hc
    exact integrable_subgroup_mul_of_hasCompactSupport _
      (GeneralLinear.UpperUnipotent.isClosed (R := F)) _ f hf hc
  integral_formula f hf hc := by
    apply integral_quotientAverage_of_real _ _ (unipotentAverage F n) (fun _ _ => rfl)
      _ _ (integral_unipotentQuotientHaar_real F n) f hf hc
    exact integrable_subgroup_mul_of_hasCompactSupport _
      (GeneralLinear.UpperUnipotent.isClosed (R := F)) _ f hf hc

/-- Existence in every rank, without assuming a quotient measure. -/
theorem unipotent_compatibleMeasureExists :
    CompatibleMeasureExists (GeneralLinear.upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) :=
  ⟨unipotentQuotientHaar F n, unipotentQuotientHaar_isCompatible F n⟩

/-- The fixed ambient and subgroup normalizations determine the compatible
quotient measure exactly. -/
theorem unipotentQuotientHaar_unique
    (ν : Measure (LeftQuotient (GeneralLinear.upperUnipotent (n + 1) F)))
    (hν : IsCompatible (GeneralLinear.upperUnipotent (n + 1) F)
      (generalLinearHaar F n) (unipotentHaar F n) ν) :
    ν = unipotentQuotientHaar F n := by
  let := hν.regular
  apply measureOfPositiveAveraging_unique
  intro f
  have h := hν.integral_formula (fun g => (f g : ℂ))
    (Complex.continuous_ofReal.comp f.continuous)
    (f.hasCompactSupport.comp_left Complex.ofReal_zero)
  simp_rw [quotientAverage_ofReal] at h
  rw [integral_complex_ofReal, integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

/-- At `n = 0` the Riesz construction equals the previously published
transport of normalized Haar measure through the trivial quotient. -/
@[simp] theorem unipotentQuotientHaar_zero
    [MeasurableSpace (Matrix.GeneralLinearGroup (Fin 1) F)]
    [BorelSpace (Matrix.GeneralLinearGroup (Fin 1) F)]
    [MeasurableSpace (GeneralLinear.upperUnipotent 1 F)]
    [BorelSpace (GeneralLinear.upperUnipotent 1 F)]
    [MeasurableSpace (LeftQuotient (GeneralLinear.upperUnipotent 1 F))]
    [BorelSpace (LeftQuotient (GeneralLinear.upperUnipotent 1 F))] :
    unipotentQuotientHaar F 0 = rankOneQuotientHaar F :=
  (unipotentQuotientHaar_unique F 0 _ (rankOneQuotientHaar_isCompatible F)).symm

end Langlands.RankinSelberg
