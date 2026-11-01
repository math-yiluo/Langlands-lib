import Langlands.Representation.GodementJacquet.ZetaLinear
import Langlands.Representation.RankinSelberg.RationalMonomialFunctionalEquation

/-! # Extending a monomial matrix equation over the coefficient span -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory RankinSelberg LocalFactor

universe uF uV

/-- A reflected monomial identity gives the normalized functional equation
on precisely its two published denominator guards. -/
theorem normalizedFunctionalEquation_of_monomial_rational_identity
    {q : ℕ} (hq : 1 < q) {c : ℂˣ} {m : ℤ} {R RDual : RationalFunctions}
    (h : RationalReflection.subst
        (spectralReflectionUnit (Nat.zero_lt_one.trans hq)) RDual =
      laurentToRatFunc (laurentMonomialUnit c m : LaurentCoefficients) * R) :
    NormalizedFunctionalEquation q 1 1 1 c 0 m R RDual := by
  intro s hR hD
  let δ := spectralReflectionUnit (Nat.zero_lt_one.trans hq)
  have href : (δ : ℂ) / spectralPoint q s = spectralPoint q (1 - s) := by
    rw [coe_spectralReflectionUnit, spectralPoint_sub_one_sub
      (Nat.zero_lt_one.trans hq), div_eq_mul_inv]
  have hD' : RationalEvaluation.RegularAt RDual ((δ : ℂ) / spectralPoint q s) := by
    rw [href]
    exact hD
  have hM := laurentToRatFunc_regular_and_eval
    (spectralUnit (Nat.zero_lt_one.trans hq) s)
    (laurentMonomialUnit c m : LaurentCoefficients)
  simp only [coe_spectralUnit] at hM
  have he := congrArg (RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)) h
  rw [RationalEvaluation.eval_subst δ
      (spectralPoint_ne_zero_of_pos (Nat.zero_lt_one.trans hq) s) hD', href,
    RationalEvaluation.eval_mul hM.1 hR, hM.2] at he
  simpa only [Polynomial.eval_one, Units.val_one, one_pow, one_mul,
    epsilonMonomial, laurentMonomialUnit, map_mul, laurentEval_C, laurentEval_T,
    coe_spectralUnit] using he

section Coefficients

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]

/-- Coefficients admitting actual values at two fixed tests with a common
reflected rational identity form a complex submodule. -/
def matrixMonomialCoefficientSubmodule
    (q : ℕ) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (Φ ΦHat : MatrixTestFunction n F) (δ : ℂˣ) (M : RationalFunctions) :
    Submodule ℂ (Langlands.GeneralLinear (n + 1) F → ℂ) where
  carrier := {f | ∃ R RDual,
    HasShiftedRationalValue q abv μ Φ f R ∧
    HasShiftedRationalValue q abv μ ΦHat (coefficientIota f) RDual ∧
    RationalReflection.subst δ RDual = M * R}
  zero_mem' := ⟨0, 0, hasShiftedRationalValue_zero q,
    hasShiftedRationalValue_zero q, by simp⟩
  add_mem' := by
    rintro f g ⟨R, D, hR, hD, he⟩ ⟨S, E, hS, hE, hf⟩
    exact ⟨R + S, D + E, hR.add hS, hD.add hE,
      by rw [map_add, he, hf, mul_add]⟩
  smul_mem' := by
    rintro a f ⟨R, D, hR, hD, he⟩
    refine ⟨RatFunc.C a * R, RatFunc.C a * D, hR.smul a, hD.smul a, ?_⟩
    simp only [← RatFunc.smul_eq_C_mul, mul_smul_comm]
    change (RationalReflection.subst δ).toLinearMap (a • D) = a • (M * R)
    rw [map_smul]
    exact congrArg (a • ·) he

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- A fixed reflected identity extends from smooth elementary coefficients
to their full complex span and to every supplied actual rational value. -/
theorem matrixMonomialIdentity_of_biSmoothGenerators
    {q : ℕ} (hq : 1 < q) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (Φ ΦHat : MatrixTestFunction n F) (δ : ℂˣ) (M : RationalFunctions)
    (hgen : ∀ (ℓ : SmoothDual ρ) (v : smoothVectors ρ),
      ∃ R RDual,
        HasShiftedRationalValue q abv μ Φ (biSmoothCoefficient ρ ℓ v) R ∧
        HasShiftedRationalValue q abv μ ΦHat
          (coefficientIota (biSmoothCoefficient ρ ℓ v)) RDual ∧
        RationalReflection.subst δ RDual = M * R)
    (f : biSmoothMatrixCoefficients ρ) (R RDual : RationalFunctions)
    (hR : HasShiftedRationalValue q abv μ Φ f.val R)
    (hD : HasShiftedRationalValue q abv μ ΦHat (coefficientIota f.val) RDual) :
    RationalReflection.subst δ RDual = M * R := by
  have hle : biSmoothMatrixCoefficients ρ ≤
      matrixMonomialCoefficientSubmodule q abv μ Φ ΦHat δ M := by
    apply Submodule.span_le.mpr
    rintro g ⟨ℓ, v, rfl⟩
    exact hgen ℓ v
  obtain ⟨S, E, hS, hE, he⟩ := hle f.property
  have hSR : S = R := hS.2.unique hq hR.2
  have hED : E = RDual := hE.2.unique hq hD.2
  simpa only [hSR, hED] using he

/-- Normalized monomial equations with one fixed unit and exponent extend
from smooth elementary coefficients to every bi-smooth coefficient. -/
theorem normalizedFunctionalEquation_of_biSmoothGenerators
    {q : ℕ} (hq : 1 < q) (abv : AbsoluteValue F ℝ)
    (μ : Measure (Langlands.GeneralLinear (n + 1) F))
    (Φ ΦHat : MatrixTestFunction n F) (c : ℂˣ) (m : ℤ)
    (hgen : ∀ (ℓ : SmoothDual ρ) (v : smoothVectors ρ),
      ∃ R RDual,
        HasShiftedRationalValue q abv μ Φ (biSmoothCoefficient ρ ℓ v) R ∧
        HasShiftedRationalValue q abv μ ΦHat
          (coefficientIota (biSmoothCoefficient ρ ℓ v)) RDual ∧
        NormalizedFunctionalEquation q 1 1 1 c 0 m R RDual)
    (f : biSmoothMatrixCoefficients ρ) (R RDual : RationalFunctions)
    (hR : HasShiftedRationalValue q abv μ Φ f.val R)
    (hD : HasShiftedRationalValue q abv μ ΦHat (coefficientIota f.val) RDual) :
    NormalizedFunctionalEquation q 1 1 1 c 0 m R RDual := by
  apply normalizedFunctionalEquation_of_monomial_rational_identity hq
  apply matrixMonomialIdentity_of_biSmoothGenerators ρ hq abv μ Φ ΦHat
    (spectralReflectionUnit (Nat.zero_lt_one.trans hq))
    (laurentToRatFunc (laurentMonomialUnit c m : LaurentCoefficients)) _ f R RDual hR hD
  intro ℓ v
  obtain ⟨S, E, hS, hE, he⟩ := hgen ℓ v
  exact ⟨S, E, hS, hE, he.rational_identity hq⟩

end Coefficients

end Langlands.GodementJacquet
