import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial

namespace Langlands.Global

/-- The normalized-polynomial separation argument underlying Henniart 1986, Lemma 4.4. -/
def GammaPolynomialSeparationStatement : Prop :=
  ∀ q : ℕ, 1 < q →
  ∀ P Pdual Q Qdual : Polynomial ℂ,
  ∀ a c : ℂˣ, ∀ m k : ℤ,
    P.eval 0 = 1 → Pdual.eval 0 = 1 →
    Q.eval 0 = 1 → Qdual.eval 0 = 1 →
    (∀ z : ℂ, z ≠ 0 →
      ¬ (P.eval z = 0 ∧ Pdual.eval ((q : ℂ)⁻¹ * z⁻¹) = 0)) →
    (∀ z : ℂ, z ≠ 0 →
      ¬ (Q.eval z = 0 ∧ Qdual.eval ((q : ℂ)⁻¹ * z⁻¹) = 0)) →
    let x : RatFunc ℂ := RatFunc.X
    let reflected : RatFunc ℂ := (RatFunc.C (q : ℂ))⁻¹ * x⁻¹
    let epsilonP : RatFunc ℂ := RatFunc.C (a : ℂ) * x ^ m
    let epsilonQ : RatFunc ℂ := RatFunc.C (c : ℂ) * x ^ k
    epsilonP * Polynomial.aeval x P / Polynomial.aeval reflected Pdual =
        epsilonQ * Polynomial.aeval x Q / Polynomial.aeval reflected Qdual →
      P = Q ∧ Pdual = Qdual ∧ epsilonP = epsilonQ

/-- Reciprocal root bounds that ensure the absence of cancellation after reflection. -/
def ReflectedRootRegionStatement : Prop :=
  ∀ q : ℕ, 1 < q →
  ∀ r : ℝ, 0 < r →
  ∀ P Pdual : Polynomial ℂ,
    (∀ z : ℂ, P.eval z = 0 → r ≤ ‖z‖) →
    (∀ z : ℂ, Pdual.eval z = 0 → r⁻¹ ≤ ‖z‖) →
    ∀ z : ℂ, z ≠ 0 →
      ¬ (P.eval z = 0 ∧ Pdual.eval ((q : ℂ)⁻¹ * z⁻¹) = 0)

/-- The algebraic separation and root-region prerequisites for separating local factors. -/
def GammaSeparationStatement : Prop :=
  GammaPolynomialSeparationStatement ∧ ReflectedRootRegionStatement

end Langlands.Global
