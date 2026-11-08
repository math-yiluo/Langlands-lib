import Langlands.Representation.Conductor.SphericalEvaluation

/-! # Linearity of the actual spherical model coefficients -/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.GeneralLinear.Iwasawa
open scoped BigOperators

universe uF uV uA uR

section FiniteSupport

variable {A : Type uA} [CommRing A]

/-- A finite coefficient sum can be taken over any finite set containing
the actual support. This allows cancellation of coefficients under addition. -/
theorem finiteLaurentCoefficientSum_eq_sum_of_support_subset
    (S : LaurentSeries A) (hS : S.support.Finite)
    (s : Finset ℤ) (hs : S.support ⊆ (s : Set ℤ)) :
    finiteLaurentCoefficientSum S hS = ∑ d ∈ s, S.coeff d := by
  classical
  apply Finset.sum_subset
  · intro d hd
    exact hs (hS.mem_toFinset.mp hd)
  · intro d _ hd
    by_contra hn
    exact hd (hS.mem_toFinset.mpr hn)

theorem finiteLaurentCoefficientSum_add (S T : LaurentSeries A)
    (hS : S.support.Finite) (hT : T.support.Finite)
    (hST : (S + T).support.Finite) :
    finiteLaurentCoefficientSum (S + T) hST =
      finiteLaurentCoefficientSum S hS + finiteLaurentCoefficientSum T hT := by
  classical
  let s := (hS.union hT).toFinset
  have hS' : S.support ⊆ (s : Set ℤ) := by
    intro d hd
    exact (hS.union hT).mem_toFinset.mpr (Or.inl hd)
  have hT' : T.support ⊆ (s : Set ℤ) := by
    intro d hd
    exact (hS.union hT).mem_toFinset.mpr (Or.inr hd)
  have hST' : (S + T).support ⊆ (s : Set ℤ) :=
    (HahnSeries.support_add_subset S T).trans (fun d hd => hd.elim (hS' (a := d)) (hT' (a := d)))
  rw [finiteLaurentCoefficientSum_eq_sum_of_support_subset _ hST s hST',
    finiteLaurentCoefficientSum_eq_sum_of_support_subset _ hS s hS',
    finiteLaurentCoefficientSum_eq_sum_of_support_subset _ hT s hT']
  simp only [HahnSeries.coeff_add, Finset.sum_add_distrib]

variable {R : Type uR} [Semiring R] [Module R A]

theorem finiteLaurentCoefficientSum_smul (a : R) (S : LaurentSeries A)
    (hS : S.support.Finite) (haS : (a • S).support.Finite) :
    finiteLaurentCoefficientSum (a • S) haS =
      a • finiteLaurentCoefficientSum S hS := by
  classical
  rw [finiteLaurentCoefficientSum_eq_sum_of_support_subset _ haS hS.toFinset
    (fun d hd => hS.mem_toFinset.mpr (HahnSeries.support_smul_subset a S hd))]
  simp only [HahnSeries.coeff_smul, finiteLaurentCoefficientSum, Finset.smul_sum]

/-- Laurent series with finite actual support form a submodule. -/
def finiteSupportLaurentSubmodule : Submodule R (LaurentSeries A) where
  carrier := {S | S.support.Finite}
  zero_mem' := by simp only [Set.mem_ofPred_eq, HahnSeries.support_zero, Set.finite_empty]
  add_mem' hS hT := (hS.union hT).subset (HahnSeries.support_add_subset _ _)
  smul_mem' a S hS := hS.subset (HahnSeries.support_smul_subset a S)

/-- Summing the coefficients is linear on the finite-support submodule. -/
def finiteLaurentCoefficientSumLinearMap :
    finiteSupportLaurentSubmodule (R := R) (A := A) →ₗ[R] A where
  toFun S := finiteLaurentCoefficientSum S.val S.property
  map_add' S T := finiteLaurentCoefficientSum_add S.val T.val S.property T.property _
  map_smul' a S := finiteLaurentCoefficientSum_smul a S.val S.property _

end FiniteSupport

section Integrand

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
variable {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
variable (q : ℕ) (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)

/-- The actual polynomial degree integrand depends linearly on its
Whittaker function, before any integration or support condition. -/
def degreeCorankOnePolynomialIntegrandLinearMap (d : ℤ) :
    WhittakerFunctions ψ (n + 1) →ₗ[ℂ]
      (LeftUnipotentQuotient n F → symmetricTorusSubalgebra (Fin (n + 1)) ℂ) where
  toFun W := degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d
  map_add' W T := by
    funext t
    simp only [Pi.add_apply]
    unfold degreeCorankOnePolynomialIntegrand
    split_ifs
    · induction t using Quotient.inductionOn with
      | h g => simp [corankOnePolynomialFunction, add_mul, add_smul]
    · simp
  map_smul' a W := by
    funext t
    simp only [Pi.smul_apply]
    unfold degreeCorankOnePolynomialIntegrand
    split_ifs
    · induction t using Quotient.inductionOn with
      | h g => simp [corankOnePolynomialFunction, mul_smul, mul_assoc]
    · simp

end Integrand

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

include hπ in
/-- The actual scalar evaluation of each degree integrand is integrable. -/
theorem degreeCorankOneModelIntegrand_evaluation_integrable
    (w : (coefficientModel π ℓ).toSubmodule)
    (x : Fin (n + 1) → ℂˣ) (d : ℤ) :
    Integrable (fun t => symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelIntegrand h π ℓ w d t)) μ := by
  exact (degreeCorankOneModelIntegrand_isScalarIntegrable π hπ ψ ℓ abv q h w d)
    ((symmetricTorusEvaluation (Fin (n + 1)) ℂ x).toLinearMap.comp
      (Submodule.span ℂ (Set.range (degreeCorankOneModelIntegrand h π ℓ w d))).subtype)

private theorem degreeCorankOneModelCoefficient_evaluation_as_integral
    (w : (coefficientModel π ℓ).toSubmodule)
    (x : Fin (n + 1) → ℂˣ) (d : ℤ) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelCoefficient h π hπ ℓ w d) =
    ∫ t, symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelIntegrand h π ℓ w d t) ∂μ := by
  simpa only [degreeCorankOneModelIntegrand,
    symmetricTorusEvaluation_degreeCorankOnePolynomialIntegrand] using
    symmetricTorusEvaluation_degreeCorankOneModelCoefficient h π hπ ℓ w x d

theorem degreeCorankOneModelCoefficient_add
    (w z : (coefficientModel π ℓ).toSubmodule) (d : ℤ) :
    degreeCorankOneModelCoefficient h π hπ ℓ (w + z) d =
      degreeCorankOneModelCoefficient h π hπ ℓ w d +
        degreeCorankOneModelCoefficient h π hπ ℓ z d := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [map_add]
  simp_rw [degreeCorankOneModelCoefficient_evaluation_as_integral]
  have he : degreeCorankOneModelIntegrand h π ℓ (w + z) d =
      degreeCorankOneModelIntegrand h π ℓ w d +
        degreeCorankOneModelIntegrand h π ℓ z d :=
    (degreeCorankOnePolynomialIntegrandLinearMap ψ abv h.uniformizer q h.conductor.1 d
      ).map_add w.val z.val
  rw [he]
  simp only [Pi.add_apply, map_add]
  exact integral_add
    (degreeCorankOneModelIntegrand_evaluation_integrable h π hπ ℓ w x d)
    (degreeCorankOneModelIntegrand_evaluation_integrable h π hπ ℓ z x d)

theorem degreeCorankOneModelCoefficient_smul (a : ℂ)
    (w : (coefficientModel π ℓ).toSubmodule) (d : ℤ) :
    degreeCorankOneModelCoefficient h π hπ ℓ (a • w) d =
      a • degreeCorankOneModelCoefficient h π hπ ℓ w d := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [map_smul]
  simp_rw [degreeCorankOneModelCoefficient_evaluation_as_integral]
  have he : degreeCorankOneModelIntegrand h π ℓ (a • w) d =
      a • degreeCorankOneModelIntegrand h π ℓ w d :=
    (degreeCorankOnePolynomialIntegrandLinearMap ψ abv h.uniformizer q h.conductor.1 d
      ).map_smul a w.val
  rw [he]
  simp only [Pi.smul_apply, map_smul]
  exact integral_smul a _

/-- Each actual integrated degree coefficient is a complex linear map of
the model vector. Integrability is supplied by smoothness, not assumed. -/
def degreeCorankOneModelCoefficientLinearMap (d : ℤ) :
    (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      symmetricTorusSubalgebra (Fin (n + 1)) ℂ where
  toFun w := degreeCorankOneModelCoefficient h π hπ ℓ w d
  map_add' w z := degreeCorankOneModelCoefficient_add h π hπ ℓ w z d
  map_smul' a w := degreeCorankOneModelCoefficient_smul h π hπ ℓ a w d

theorem corankOneModelLaurentSeries_add
    (w z : (coefficientModel π ℓ).toSubmodule) :
    corankOneModelLaurentSeries h π hπ ℓ (w + z) =
      corankOneModelLaurentSeries h π hπ ℓ w +
        corankOneModelLaurentSeries h π hπ ℓ z := by
  apply HahnSeries.ext
  funext d
  exact degreeCorankOneModelCoefficient_add h π hπ ℓ w z d

theorem corankOneModelLaurentSeries_smul (a : ℂ)
    (w : (coefficientModel π ℓ).toSubmodule) :
    corankOneModelLaurentSeries h π hπ ℓ (a • w) =
      a • corankOneModelLaurentSeries h π hπ ℓ w := by
  apply HahnSeries.ext
  funext d
  exact degreeCorankOneModelCoefficient_smul h π hπ ℓ a w d

/-- The actual model Laurent series is linear before any finite-support
or functional-equation assertion. -/
def corankOneModelLaurentSeriesLinearMap :
    (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      LaurentSeries (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) where
  toFun w := corankOneModelLaurentSeries h π hπ ℓ w
  map_add' w z := corankOneModelLaurentSeries_add h π hπ ℓ w z
  map_smul' a w := corankOneModelLaurentSeries_smul h π hπ ℓ a w

theorem corankOneModelDenominatorProduct_add
    (w z : (coefficientModel π ℓ).toSubmodule) (P : Polynomial ℂ) :
    corankOneModelDenominatorProduct h π hπ ℓ (w + z) P =
      corankOneModelDenominatorProduct h π hπ ℓ w P +
        corankOneModelDenominatorProduct h π hπ ℓ z P := by
  simp only [corankOneModelDenominatorProduct, corankOneModelLaurentSeries_add, add_mul]

theorem corankOneModelDenominatorProduct_smul (a : ℂ)
    (w : (coefficientModel π ℓ).toSubmodule) (P : Polynomial ℂ) :
    corankOneModelDenominatorProduct h π hπ ℓ (a • w) P =
      a • corankOneModelDenominatorProduct h π hπ ℓ w P := by
  apply HahnSeries.ext
  funext d
  simp only [HahnSeries.coeff_smul, corankOneModelDenominatorProduct_coeff,
    degreeCorankOneModelCoefficient_smul, smul_mul_assoc, Finset.smul_sum]

/-- Multiplication by the fixed coordinate denominator preserves linearity. -/
def corankOneModelDenominatorProductLinearMap (P : Polynomial ℂ) :
    (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      LaurentSeries (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) where
  toFun w := corankOneModelDenominatorProduct h π hπ ℓ w P
  map_add' w z := corankOneModelDenominatorProduct_add h π hπ ℓ w z P
  map_smul' a w := corankOneModelDenominatorProduct_smul h π hπ ℓ a w P

/-- Actual model vectors whose product with the chosen denominator has
finite support. No assertion that every model vector belongs is made. -/
def corankOneFiniteSupportModelVectors (P : Polynomial ℂ) :
    Submodule ℂ (coefficientModel π ℓ).toSubmodule where
  carrier := {w | (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite}
  zero_mem' := by
    have hz := (corankOneModelDenominatorProductLinearMap h π hπ ℓ P).map_zero
    change corankOneModelDenominatorProduct h π hπ ℓ 0 P = 0 at hz
    simp only [Set.mem_ofPred_eq, hz, HahnSeries.support_zero, Set.finite_empty]
  add_mem' {w z} hw hz := by
    change (corankOneModelDenominatorProduct h π hπ ℓ (w + z) P).support.Finite
    rw [corankOneModelDenominatorProduct_add]
    exact (hw.union hz).subset (HahnSeries.support_add_subset _ _)
  smul_mem' a w hw := by
    change (corankOneModelDenominatorProduct h π hπ ℓ (a • w) P).support.Finite
    rw [corankOneModelDenominatorProduct_smul]
    exact hw.subset (HahnSeries.support_smul_subset a _)

/-- The actual symmetric numerator is linear on the model vectors with
finite denominator product. -/
def corankOneModelNumeratorLinearMap (P : Polynomial ℂ) :
    corankOneFiniteSupportModelVectors h π hπ ℓ P →ₗ[ℂ]
      symmetricTorusSubalgebra (Fin (n + 1)) ℂ where
  toFun w := corankOneModelNumerator h π hπ ℓ w.val P w.property
  map_add' w z := by
    unfold corankOneModelNumerator
    simp only [Submodule.coe_add, corankOneModelDenominatorProduct_add]
    exact finiteLaurentCoefficientSum_add _ _ w.property z.property _
  map_smul' a w := by
    unfold corankOneModelNumerator
    simp only [Submodule.coe_smul, corankOneModelDenominatorProduct_smul]
    exact finiteLaurentCoefficientSum_smul a _ w.property _

@[simp] theorem corankOneModelNumeratorLinearMap_apply (P : Polynomial ℂ)
    (w : corankOneFiniteSupportModelVectors h π hπ ℓ P) :
    corankOneModelNumeratorLinearMap h π hπ ℓ P w =
      corankOneModelNumerator h π hπ ℓ w.val P w.property := rfl

/-- The actual finite numerators form a complex vector subspace. Stability
under multiplication by symmetric Laurent polynomials is a separate result. -/
def corankOneModelNumeratorSubmodule (P : Polynomial ℂ) :
    Submodule ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) :=
  (corankOneModelNumeratorLinearMap h π hπ ℓ P).range

theorem mem_corankOneModelNumeratorSubmodule_iff (P : Polynomial ℂ)
    (a : symmetricTorusSubalgebra (Fin (n + 1)) ℂ) :
    a ∈ corankOneModelNumeratorSubmodule h π hπ ℓ P ↔
      ∃ (w : (coefficientModel π ℓ).toSubmodule)
        (hw : (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite),
        corankOneModelNumerator h π hπ ℓ w P hw = a := by
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.val, w.property, rfl⟩
  · rintro ⟨w, hw, ha⟩
    exact ⟨⟨w, hw⟩, ha⟩

end Model

end Langlands.Conductor
