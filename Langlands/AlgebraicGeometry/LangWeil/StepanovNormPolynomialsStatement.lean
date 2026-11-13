import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveHasseWeilStatement
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Roots

/-!
# The auxiliary norm polynomials in Schmidt's method

This proposition isolates the polynomial construction, before the final point-count
and parameter estimates, including higher differentials for arbitrary finite fields.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- Schmidt's auxiliary norm polynomials, with root multiplicities rather than vanishing
Hasse derivatives. The good set omits fewer than `2mn` abscissae. The two polynomials
control the rational roots and their complement among the `n` geometric roots. -/
def StepanovNormPolynomialsStatement : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (f : MvPolynomial (Fin 2) F),
    Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) →
    MvPolynomial.pderiv 0 f ≠ 0 → MvPolynomial.pderiv 1 f ≠ 0 →
    2 ≤ f.degreeOf 1 → f.degreeOf 1 ≤ f.degreeOf 0 →
    let m := f.degreeOf 0
    let n := f.degreeOf 1
    let q := Nat.card F
    let r := fun x : F =>
      Nat.card {y : F // MvPolynomial.eval ![x, y] f = 0}
    ∀ M : ℕ, 0 < M →
      M ^ 2 * (n ^ 2 + 1) + (M + m) * n ^ 2 < q → M * n ≤ q →
      ∃ (s : Finset F) (h₁ h₂ : Polynomial F),
        q < s.card + 2 * m * n ∧
        (∀ x : F, r x ≤ n) ∧
        h₁ ≠ 0 ∧ h₂ ≠ 0 ∧
        h₁.natDegree < q * (M + (2 * m * (n - 1) + 1)) ∧
        h₂.natDegree < q * ((n - 1) * M + (2 * m * (n - 1) + 1)) ∧
        ∀ x ∈ s,
          M * r x ≤ h₁.rootMultiplicity x ∧
          M * (n - r x) ≤ h₂.rootMultiplicity x

end Langlands.AlgebraicGeometry.LangWeil
