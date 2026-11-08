import Langlands.Representation.Conductor.SphericalTransform
import Langlands.Representation.Conductor.SphericalFiniteness
import Langlands.Representation.Conductor.CoefficientIntegral
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Degree coefficients of the actual Laurent quotient integrand
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.GeneralLinear.Iwasawa

universe uF

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
variable {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
variable (q : ℕ) (W : WhittakerFunctions ψ (n + 1))
variable (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)

/-- The actual value span of one degree-restricted Laurent integrand. -/
abbrev degreeCorankOnePolynomialSpan (d : ℤ) :
    Submodule ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) :=
  Submodule.span ℂ
    (Set.range (degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d))

/-- Compact support in the actual quotient implies finite-dimensionality of
the degree integrand's value span. -/
theorem degreeCorankOnePolynomialSpan_finite_of_compactSupport
    [IsNonarchimedeanLocalField F] (d : ℤ)
    {D : Set (LeftUnipotentQuotient n F)} (hD : IsCompact D)
    (hSupport : Function.support
      (degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d) ⊆ D) :
    Module.Finite ℂ (degreeCorankOnePolynomialSpan ψ abv hϖ q W hψ d) := by
  classical
  obtain ⟨M, hM, hvalues⟩ :=
    sphericalWhittakerPolynomial_finiteDimensional_on_quotientCompact hϖ
      (inverseStandardCharacter ψ n) q
      (isIntegrallyTrivial_inverseStandardCharacter hψ n) hD
  have hmem (t : LeftUnipotentQuotient n F) :
      degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d t ∈ M := by
    by_cases ht : t ∈ D
    · induction t using Quotient.inductionOn with
      | h g =>
        unfold degreeCorankOnePolynomialIntegrand
        split_ifs
        · exact M.smul_mem _ (hvalues g ht)
        · exact M.zero_mem
    · have hz : degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d t = 0 := by
        by_contra hne
        exact ht (hSupport hne)
      rw [hz]
      exact M.zero_mem
  let : Module.Finite ℂ M := hM
  apply Submodule.finiteDimensional_of_le (S₂ := M)
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  exact hmem t

variable [MeasurableSpace (LeftUnipotentQuotient n F)]

/-- The Laurent coefficient of one Iwasawa degree, integrated in the actual
finite-dimensional value span. -/
def degreeCorankOneCoefficient (μ : Measure (LeftUnipotentQuotient n F)) (d : ℤ)
    [Module.Finite ℂ (degreeCorankOnePolynomialSpan ψ abv hϖ q W hψ d)] :
    symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  finiteSpanCoefficientIntegral μ
    (degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d)

/-- Integration preserves the degree of the Laurent coefficient. -/
theorem degreeCorankOneCoefficient_isHomogeneous
    (μ : Measure (LeftUnipotentQuotient n F)) (d : ℤ)
    [Module.Finite ℂ (degreeCorankOnePolynomialSpan ψ abv hϖ q W hψ d)] :
    IsSymmetricTorusHomogeneous (Fin (n + 1)) ℂ
      (degreeCorankOneCoefficient ψ abv hϖ q W hψ μ d) d := by
  exact finiteSpanCoefficientIntegral_mem μ
    (degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d)
    (symmetricTorusHomogeneousSubmodule (Fin (n + 1)) ℂ d)
    (degreeCorankOnePolynomialIntegrand_isHomogeneous ψ abv hϖ q W hψ d)

/-- Unit-tuple evaluation of a coefficient is the actual scalar
degree-restricted quotient integral, under scalar integrability. -/
theorem symmetricTorusEvaluation_degreeCorankOneCoefficient
    (μ : Measure (LeftUnipotentQuotient n F)) (d : ℤ)
    [Module.Finite ℂ (degreeCorankOnePolynomialSpan ψ abv hϖ q W hψ d)]
    (hf : IsScalarIntegrable μ (coefficientSpanFunction
      (degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d)))
    (x : Fin (n + 1) → ℂˣ) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneCoefficient ψ abv hϖ q W hψ μ d) =
    ∫ t, (if sphericalQuotientDegree hϖ t = d then
      corankOneIntegrand ψ abv W (inverseSphericalWhittaker hψ hϖ q x) 0 t
      else 0) ∂μ := by
  simpa only [degreeCorankOneCoefficient, AlgHom.toLinearMap_apply,
    symmetricTorusEvaluation_degreeCorankOnePolynomialIntegrand] using
    finiteSpanCoefficientIntegral_linear_eval μ _ hf
      (symmetricTorusEvaluation (Fin (n + 1)) ℂ x).toLinearMap

end Langlands.Conductor
