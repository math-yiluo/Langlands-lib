import Langlands.Representation.Conductor.SphericalHomogeneity
import Langlands.Representation.Conductor.Essential

/-!
# Laurent coefficients on the actual corank-one quotient
-/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg Langlands.QuotientIntegration
open Langlands.GeneralLinear.Iwasawa

universe uF uK uσ

section Homogeneous

variable (σ : Type uσ) (K : Type uK) [Fintype σ] [Field K]

/-- The subspace of symmetric Laurent elements of a fixed integral degree. -/
def symmetricTorusHomogeneousSubmodule (d : ℤ) :
    Submodule K (symmetricTorusSubalgebra σ K) where
  carrier := {p | IsSymmetricTorusHomogeneous σ K p d}
  zero_mem' := by intro c; simp
  add_mem' := by
    intro p r hp hr c
    rw [map_add, hp c, hr c, mul_add]
  smul_mem' := by
    intro a p hp c
    simp only [Algebra.smul_def]
    rw [map_mul, AlgHom.commutes, hp c]
    ring

@[simp] theorem mem_symmetricTorusHomogeneousSubmodule
    (d : ℤ) (p : symmetricTorusSubalgebra σ K) :
    p ∈ symmetricTorusHomogeneousSubmodule σ K d ↔
      IsSymmetricTorusHomogeneous σ K p d := Iff.rfl

end Homogeneous

section QuotientFunction

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {n : ℕ} (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
variable {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)
variable (q : ℕ) (W : WhittakerFunctions ψ (n + 1))

/-- The Laurent-valued corank-one integrand at spectral value zero, before
passing to the unipotent quotient. -/
def corankOnePolynomialFunction (g : Langlands.GeneralLinear (n + 1) F) :
    symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  (W.val (rankInclusion 1 g) * determinantWeight abv g (0 - 1 / 2)) •
    sphericalWhittakerPolynomial hϖ (inverseStandardCharacter ψ n) q g

@[simp] theorem symmetricTorusEvaluation_corankOnePolynomialFunction
    (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
    (x : Fin (n + 1) → ℂˣ) (g : Langlands.GeneralLinear (n + 1) F) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (corankOnePolynomialFunction ψ abv hϖ q W g) =
    corankOneFunction ψ abv W (inverseSphericalWhittaker hψ hϖ q x) 0 g := by
  simp only [corankOnePolynomialFunction, map_smul,
    symmetricTorusEvaluation_sphericalWhittakerPolynomial, smul_eq_mul,
    corankOneFunction, inverseSphericalWhittaker_apply]
  ring

/-- Evaluation separation proves representative independence in the actual
Laurent algebra. -/
theorem corankOnePolynomialFunction_invariant
    (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
    (u : upperUnipotent (n + 1) F) (g : Langlands.GeneralLinear (n + 1) F) :
    corankOnePolynomialFunction ψ abv hϖ q W (u.val * g) =
      corankOnePolynomialFunction ψ abv hϖ q W g := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [symmetricTorusEvaluation_corankOnePolynomialFunction ψ abv hϖ q W hψ,
    symmetricTorusEvaluation_corankOnePolynomialFunction ψ abv hϖ q W hψ]
  exact corankOneFunction_invariant ψ abv W _ 0 u g

/-- The Laurent-valued integrand on the actual left-unipotent quotient. -/
def corankOnePolynomialIntegrand
    (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1) :
    LeftUnipotentQuotient n F → symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  descend _ (corankOnePolynomialFunction ψ abv hϖ q W)
    (corankOnePolynomialFunction_invariant ψ abv hϖ q W hψ)

@[simp] theorem corankOnePolynomialIntegrand_mk
    (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
    (g : Langlands.GeneralLinear (n + 1) F) :
    corankOnePolynomialIntegrand ψ abv hϖ q W hψ (Quotient.mk _ g) =
      corankOnePolynomialFunction ψ abv hϖ q W g := rfl

@[simp] theorem symmetricTorusEvaluation_corankOnePolynomialIntegrand
    (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)
    (x : Fin (n + 1) → ℂˣ) (t : LeftUnipotentQuotient n F) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (corankOnePolynomialIntegrand ψ abv hϖ q W hψ t) =
    corankOneIntegrand ψ abv W (inverseSphericalWhittaker hψ hϖ q x) 0 t := by
  induction t using Quotient.inductionOn with
  | h g => exact symmetricTorusEvaluation_corankOnePolynomialFunction ψ abv hϖ q W hψ x g

omit [TopologicalSpace F] in
/-- The sum of Iwasawa exponents descends to the actual quotient. -/
def sphericalQuotientDegree : LeftUnipotentQuotient n F → ℤ :=
  descend _ (fun g => ∑ i, exponent hϖ g i) (by
    intro u g
    rw [exponent_unipotent_mul hϖ g u.property])

omit [TopologicalSpace F] in
@[simp] theorem sphericalQuotientDegree_mk (g : Langlands.GeneralLinear (n + 1) F) :
    sphericalQuotientDegree hϖ (Quotient.mk _ g) = ∑ i, exponent hϖ g i := rfl

variable (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)

/-- At each quotient point the Laurent integrand has its Iwasawa degree. -/
theorem corankOnePolynomialIntegrand_isHomogeneous (t : LeftUnipotentQuotient n F) :
    IsSymmetricTorusHomogeneous (Fin (n + 1)) ℂ
      (corankOnePolynomialIntegrand ψ abv hϖ q W hψ t)
      (sphericalQuotientDegree hϖ t) := by
  induction t using Quotient.inductionOn with
  | h g =>
    exact (symmetricTorusHomogeneousSubmodule (Fin (n + 1)) ℂ
      (∑ i, exponent hϖ g i)).smul_mem _
      (sphericalWhittakerPolynomial_isHomogeneous hϖ (inverseStandardCharacter ψ n) q g)

open scoped Classical in
/-- Restriction of the actual Laurent integrand to one integral degree,
extended by zero on the complement. -/
def degreeCorankOnePolynomialIntegrand (d : ℤ) (t : LeftUnipotentQuotient n F) :
    symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  if sphericalQuotientDegree hϖ t = d then
    corankOnePolynomialIntegrand ψ abv hϖ q W hψ t else 0

theorem degreeCorankOnePolynomialIntegrand_isHomogeneous
    (d : ℤ) (t : LeftUnipotentQuotient n F) :
    IsSymmetricTorusHomogeneous (Fin (n + 1)) ℂ
      (degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d t) d := by
  classical
  unfold degreeCorankOnePolynomialIntegrand
  split_ifs with ht
  · rw [← ht]
    exact corankOnePolynomialIntegrand_isHomogeneous ψ abv hϖ q W hψ t
  · exact (symmetricTorusHomogeneousSubmodule (Fin (n + 1)) ℂ d).zero_mem

@[simp] theorem symmetricTorusEvaluation_degreeCorankOnePolynomialIntegrand
    (x : Fin (n + 1) → ℂˣ) (d : ℤ) (t : LeftUnipotentQuotient n F) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOnePolynomialIntegrand ψ abv hϖ q W hψ d t) =
    if sphericalQuotientDegree hϖ t = d then
      corankOneIntegrand ψ abv W (inverseSphericalWhittaker hψ hϖ q x) 0 t else 0 := by
  classical
  unfold degreeCorankOnePolynomialIntegrand
  split_ifs
  · exact symmetricTorusEvaluation_corankOnePolynomialIntegrand ψ abv hϖ q W hψ x t
  · exact map_zero _

end QuotientFunction

end Langlands.Conductor
