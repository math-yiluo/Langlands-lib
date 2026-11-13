import Langlands.Representation.Conductor.SphericalProduct
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Uniform upper degree bounds from pointwise ones

A complex polynomial vanishing on a nonempty open set is zero. With the Baire category
theorem on `ℂ^σ` this gives: if a family `c_d` of Laurent polynomials indexed by the
integers has, at every tuple of units `x`, values `c_d(x)` that vanish for all large `d`,
then one bound works for every `x`, and `c_d = 0` beyond it. Applied to the actual model
denominator product, pointwise finite upper bounds give finite support over the symmetric
Laurent algebra.
-/

noncomputable section

namespace Langlands.Conductor

open MvPolynomial
open scoped BigOperators

universe uσ uF uV

section Baire

variable {σ : Type uσ} [Fintype σ]

/-- A complex polynomial vanishing on a nonempty open subset of `ℂ^σ` is zero. -/
theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_open (p : MvPolynomial σ ℂ)
    {U : Set (σ → ℂ)} (hU : IsOpen U) (hne : U.Nonempty)
    (hp : ∀ z ∈ U, eval z p = 0) : p = 0 := by
  obtain ⟨z₀, hz₀⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  apply MvPolynomial.funext_set (fun i => Metric.ball (z₀ i) r)
  · intro i
    exact infinite_of_mem_nhds (z₀ i) (Metric.ball_mem_nhds _ hr)
  · intro z hz
    rw [map_zero]
    apply hp
    apply hball
    rw [ball_pi _ hr]
    exact hz

/-- A Laurent polynomial times a power of the coordinate product is a polynomial, at
every tuple of units; if that polynomial is zero, so is the Laurent polynomial. -/
theorem torusPolynomial_exists_numerator (p : TorusPolynomialAlgebra σ ℂ) :
    ∃ (m : ℕ) (a : MvPolynomial σ ℂ),
      (∀ x : σ → ℂˣ, torusPolynomialEvaluation σ ℂ x p * (∏ i, (x i : ℂ)) ^ m =
        eval (fun i => (x i : ℂ)) a) ∧ (a = 0 → p = 0) := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (∏ i : σ, (X i : MvPolynomial σ ℂ)) p
  refine ⟨m, a, fun x => ?_, fun h0 => ?_⟩
  · have he := congrArg (torusPolynomialEvaluation σ ℂ x) ha
    rw [map_mul, map_pow, torusPolynomialEvaluation_algebraMap,
      torusPolynomialEvaluation_algebraMap] at he
    simp only [map_prod, aeval_X] at he
    exact he
  · rw [h0, map_zero] at ha
    exact ((IsLocalization.Away.algebraMap_isUnit
      (S := TorusPolynomialAlgebra σ ℂ) (∏ i : σ, (X i : MvPolynomial σ ℂ))).pow m
        ).mul_left_eq_zero.mp ha

/-- **Uniform bound.** If at every tuple of units the values of a family of Laurent
polynomials vanish beyond some degree, then the family itself vanishes beyond one
common degree. The proof is the Baire category theorem on `ℂ^σ`. -/
theorem torusPolynomial_exists_upper_bound (c : ℤ → TorusPolynomialAlgebra σ ℂ)
    (h : ∀ x : σ → ℂˣ, ∃ B : ℤ, ∀ d, B < d → torusPolynomialEvaluation σ ℂ x (c d) = 0) :
    ∃ B : ℤ, ∀ d, B < d → c d = 0 := by
  choose m a ha hzero using fun d => torusPolynomial_exists_numerator (c d)
  let f : σ ⊕ ℤ → Set (σ → ℂ) := fun j => match j with
    | Sum.inl i => {z | eval z (X i : MvPolynomial σ ℂ) = 0}
    | Sum.inr B => {z | ∀ d, B < d → eval z (a d) = 0}
  have hclosed : ∀ j, IsClosed (f j) := by
    intro j
    cases j with
    | inl i => exact isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
    | inr B =>
      change IsClosed {z : σ → ℂ | ∀ d, B < d → eval z (a d) = 0}
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun d => isClosed_iInter fun _ =>
        isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have hunion : ⋃ j, f j = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    rw [Set.mem_iUnion]
    by_cases hz : ∀ i, z i ≠ 0
    · let x : σ → ℂˣ := fun i => Units.mk0 (z i) (hz i)
      obtain ⟨B, hB⟩ := h x
      refine ⟨Sum.inr B, fun d hd => ?_⟩
      have he := ha d x
      rw [hB d hd, zero_mul] at he
      exact he.symm
    · push Not at hz
      obtain ⟨i, hi⟩ := hz
      exact ⟨Sum.inl i, by simp [f, hi]⟩
  obtain ⟨j, hj⟩ := nonempty_interior_of_iUnion_of_closed hclosed hunion
  have hsub : ∀ z ∈ interior (f j), z ∈ f j := fun z hz => interior_subset hz
  cases j with
  | inl i =>
    exfalso
    exact X_ne_zero i (mvPolynomial_eq_zero_of_eval_eq_zero_on_open _ isOpen_interior hj
      (fun z hz => hsub z hz))
  | inr B =>
    refine ⟨B, fun d hd => hzero d ?_⟩
    exact mvPolynomial_eq_zero_of_eval_eq_zero_on_open _ isOpen_interior hj
      (fun z hz => hsub z hz d hd)

/-- The same uniform bound for a Laurent series over the symmetric Laurent algebra:
pointwise finite upper bounds of its specializations give one bound for all of them. -/
theorem symmetricTorusLaurentSeries_exists_upper_bound
    (S : LaurentSeries (symmetricTorusSubalgebra σ ℂ))
    (h : ∀ x : σ → ℂˣ, ∃ B : ℤ, ∀ d, B < d →
      (S.map (symmetricTorusEvaluation σ ℂ x)).coeff d = 0) :
    ∃ B : ℤ, ∀ (x : σ → ℂˣ) (d : ℤ), B < d →
      (S.map (symmetricTorusEvaluation σ ℂ x)).coeff d = 0 := by
  obtain ⟨B, hB⟩ := torusPolynomial_exists_upper_bound (fun d => (S.coeff d).val) h
  refine ⟨B, fun x d hd => ?_⟩
  change symmetricTorusEvaluation σ ℂ x (S.coeff d) = 0
  have hd' : S.coeff d = 0 := Subtype.ext (hB d hd)
  rw [hd', map_zero]

end Baire

section Model

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg

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
variable (w : (coefficientModel π ℓ).toSubmodule) (P : Polynomial ℂ)

/-- If every specialization of the actual model denominator product vanishes beyond
some degree depending on the tuple, the product has finite support over the symmetric
Laurent algebra. -/
theorem corankOneModelDenominatorProduct_support_finite_of_pointwise
    (hpt : ∀ x : Fin (n + 1) → ℂˣ, ∃ B : ℤ, ∀ d, B < d →
      ((corankOneModelDenominatorProduct h π hπ ℓ w P).map
        (symmetricTorusEvaluation (Fin (n + 1)) ℂ x)).coeff d = 0) :
    (corankOneModelDenominatorProduct h π hπ ℓ w P).support.Finite := by
  obtain ⟨B, hB⟩ := symmetricTorusLaurentSeries_exists_upper_bound _ hpt
  exact corankOneModelDenominatorProduct_support_finite h π hπ ℓ w P B hB

end Model

end Langlands.Conductor
