import Langlands.Representation.Conductor.SphericalTranslation

/-! # Central translation of actual finite spherical numerators -/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.GeneralLinear.Iwasawa Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.HarmonicAnalysis
open scoped BigOperators

universe uA uF uV

section FiniteCoefficients

variable {A : Type uA} [CommRing A]

theorem laurentSingleMul_support_subset (S : LaurentSeries A) (b : ℤ) (r : A) :
    (HahnSeries.single b r * S).support ⊆ (fun d => d + b) '' S.support := by
  intro d hd
  refine ⟨d - b, ?_, sub_add_cancel d b⟩
  change S.coeff (d - b) ≠ 0
  intro hz
  exact hd (by rw [HahnSeries.coeff_single_mul, hz, mul_zero])

theorem laurentSingleMul_support_finite (S : LaurentSeries A)
    (hS : S.support.Finite) (b : ℤ) (r : A) :
    (HahnSeries.single b r * S).support.Finite :=
  (hS.image (fun d => d + b)).subset (laurentSingleMul_support_subset S b r)

/-- Summing all coefficients forgets the shift in degree while retaining
the coefficient multiplier. Actual support may shrink by cancellation. -/
theorem finiteLaurentCoefficientSum_single_mul (S : LaurentSeries A)
    (hS : S.support.Finite) (b : ℤ) (r : A)
    (hT : (HahnSeries.single b r * S).support.Finite) :
    finiteLaurentCoefficientSum (HahnSeries.single b r * S) hT =
      r * finiteLaurentCoefficientSum S hS := by
  classical
  let e : ℤ ↪ ℤ := ⟨fun d => d + b, fun _ _ h => add_right_cancel h⟩
  rw [finiteLaurentCoefficientSum_eq_sum_of_support_subset _ hT
    (hS.toFinset.map e) (by
      intro d hd
      obtain ⟨a, ha, rfl⟩ := laurentSingleMul_support_subset S b r hd
      exact Finset.mem_map.mpr ⟨a, hS.mem_toFinset.mpr ha, rfl⟩)]
  rw [Finset.sum_map, finiteLaurentCoefficientSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  change (HahnSeries.single b r * S).coeff (d + b) = r * S.coeff d
  exact HahnSeries.coeff_single_mul_add

end FiniteCoefficients

section Model

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)

theorem corankOneModelLaurentSeries_centralTranslate
    (t : ℤ) (w : (coefficientModel π ℓ).toSubmodule) :
    corankOneModelLaurentSeries h π hπ ℓ
      (corankOneCentralTranslate π ℓ ϖ t w) =
      HahnSeries.single (-((n + 1 : ℕ) * t))
        (corankOneCentralTranslationFactor abv ϖ t) *
          corankOneModelLaurentSeries h π hπ ℓ w := by
  apply HahnSeries.ext
  funext d
  simp only [HahnSeries.coeff_single_mul, sub_neg_eq_add,
    corankOneModelLaurentSeries_coeff, degreeCorankOneModelCoefficient_centralTranslate]

theorem corankOneModelDenominatorProduct_centralTranslate
    (t : ℤ) (w : (coefficientModel π ℓ).toSubmodule) (P : Polynomial ℂ) :
    corankOneModelDenominatorProduct h π hπ ℓ
      (corankOneCentralTranslate π ℓ ϖ t w) P =
      HahnSeries.single (-((n + 1 : ℕ) * t))
        (corankOneCentralTranslationFactor abv ϖ t) *
          corankOneModelDenominatorProduct h π hπ ℓ w P := by
  simp only [corankOneModelDenominatorProduct,
    corankOneModelLaurentSeries_centralTranslate, mul_assoc]

/-- Central translation preserves the actual finite-support condition. -/
theorem corankOneModelDenominatorProduct_centralTranslate_support_finite
    (t : ℤ) (w : (coefficientModel π ℓ).toSubmodule) (P : Polynomial ℂ)
    (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite) :
    (corankOneModelDenominatorProduct h π hπ ℓ
      (corankOneCentralTranslate π ℓ ϖ t w) P).support.Finite := by
  rw [corankOneModelDenominatorProduct_centralTranslate]
  exact laurentSingleMul_support_finite _ hw _ _

/-- Restrict the actual central model action to the vectors with finite
denominator product. -/
def corankOneFiniteSupportCentralTranslate (P : Polynomial ℂ) (t : ℤ) :
    Module.End ℂ (corankOneFiniteSupportModelVectors h π hπ ℓ P) where
  toFun w := ⟨corankOneCentralTranslate π ℓ ϖ t w.val,
    corankOneModelDenominatorProduct_centralTranslate_support_finite
      h π hπ ℓ t w.val P w.property⟩
  map_add' w z := by
    apply Subtype.ext
    exact (corankOneCentralTranslate π ℓ ϖ t).map_add w.val z.val
  map_smul' a w := by
    apply Subtype.ext
    exact (corankOneCentralTranslate π ℓ ϖ t).map_smul a w.val

@[simp] theorem corankOneFiniteSupportCentralTranslate_apply
    (P : Polynomial ℂ) (t : ℤ)
    (w : corankOneFiniteSupportModelVectors h π hπ ℓ P) :
    (corankOneFiniteSupportCentralTranslate h π hπ ℓ P t w).val =
      corankOneCentralTranslate π ℓ ϖ t w.val := rfl

/-- The numerator acquires the coordinate-product factor and the nonzero
scalar determinant weight; the shift of Laurent degree disappears in the sum. -/
theorem corankOneModelNumerator_centralTranslate
    (t : ℤ) (w : (coefficientModel π ℓ).toSubmodule) (P : Polynomial ℂ)
    (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite)
    (htw : (corankOneModelDenominatorProduct h π hπ ℓ
      (corankOneCentralTranslate π ℓ ϖ t w) P).support.Finite) :
    corankOneModelNumerator h π hπ ℓ
      (corankOneCentralTranslate π ℓ ϖ t w) P htw =
      corankOneCentralTranslationFactor abv ϖ t *
        corankOneModelNumerator h π hπ ℓ w P hw := by
  unfold corankOneModelNumerator
  simp only [corankOneModelDenominatorProduct_centralTranslate]
  exact finiteLaurentCoefficientSum_single_mul _ hw _ _ _

theorem corankOneModelNumeratorLinearMap_centralTranslate
    (P : Polynomial ℂ) (t : ℤ)
    (w : corankOneFiniteSupportModelVectors h π hπ ℓ P) :
    corankOneModelNumeratorLinearMap h π hπ ℓ P
      (corankOneFiniteSupportCentralTranslate h π hπ ℓ P t w) =
      corankOneCentralTranslationFactor abv ϖ t *
        corankOneModelNumeratorLinearMap h π hπ ℓ P w := by
  exact corankOneModelNumerator_centralTranslate h π hπ ℓ t w.val P w.property _

theorem corankOneCentralTranslationFactor_mul_mem_numeratorSubmodule
    (P : Polynomial ℂ) (t : ℤ) (a : symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
    (ha : a ∈ corankOneModelNumeratorSubmodule h π hπ ℓ P) :
    corankOneCentralTranslationFactor abv ϖ t * a ∈
      corankOneModelNumeratorSubmodule h π hπ ℓ P := by
  obtain ⟨w, hw, rfl⟩ :=
    (mem_corankOneModelNumeratorSubmodule_iff h π hπ ℓ P a).mp ha
  have htw := corankOneModelDenominatorProduct_centralTranslate_support_finite
    h π hπ ℓ t w P hw
  apply (mem_corankOneModelNumeratorSubmodule_iff h π hπ ℓ P _).mpr
  exact ⟨corankOneCentralTranslate π ℓ ϖ t w, htw,
    corankOneModelNumerator_centralTranslate h π hπ ℓ t w P hw htw⟩

/-- The actual numerator subspace is stable under every integral power of
the symmetric coordinate product. The scalar determinant weight is absorbed
using complex linearity of that subspace. -/
theorem determinantUnit_zpow_mul_mem_numeratorSubmodule
    (P : Polynomial ℂ) (t : ℤ) (a : symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
    (ha : a ∈ corankOneModelNumeratorSubmodule h π hπ ℓ P) :
    (symmetricTorusDeterminantUnit (Fin (n + 1)) ℂ ^ t :
      (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)ˣ) * a ∈
      corankOneModelNumeratorSubmodule h π hπ ℓ P := by
  have hm := corankOneCentralTranslationFactor_mul_mem_numeratorSubmodule
    h π hπ ℓ P (-t) a ha
  have hD := determinantWeight_ne_zero abv
    (torus ϖ (fun _ : Fin (n + 1) => -t)) (0 - 1 / 2)
  have hs := (corankOneModelNumeratorSubmodule h π hπ ℓ P).smul_mem
    (determinantWeight abv (torus ϖ (fun _ : Fin (n + 1) => -t)) (0 - 1 / 2)) hm
  simpa only [corankOneCentralTranslationFactor, neg_neg, Algebra.smul_def,
    ← mul_assoc, ← map_mul, mul_inv_cancel₀ hD, map_one, one_mul] using hs

end Model

end Langlands.Conductor
