import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveHasseWeilStatement
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Elementary coordinate reductions for absolutely irreducible plane curves

Frobenius extraction and exchange of coordinates preserve the rational zero count.
The linear-in-one-coordinate case is controlled without the norm construction.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- Elementary reductions used before applying Schmidt's norm construction. The first
clause removes coordinate inseparability and orders the partial degrees; the second
counts the fibres of a polynomial linear in its second coordinate. -/
def PlaneCurveElementaryReductionsStatement : Prop :=
  (∀ (F : Type u) [Field F] [Finite F] (f : MvPolynomial (Fin 2) F),
    Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) →
    0 < f.degreeOf 0 → 0 < f.degreeOf 1 →
    ∃ g : MvPolynomial (Fin 2) F,
      Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) g) ∧
      MvPolynomial.pderiv 0 g ≠ 0 ∧ MvPolynomial.pderiv 1 g ≠ 0 ∧
      0 < g.degreeOf 1 ∧ g.degreeOf 1 ≤ g.degreeOf 0 ∧
      g.degreeOf 0 ≤ max (f.degreeOf 0) (f.degreeOf 1) ∧
      g.degreeOf 1 ≤ min (f.degreeOf 0) (f.degreeOf 1) ∧
      Nat.card {v : Fin 2 → F // MvPolynomial.eval v g = 0} =
        Nat.card {v : Fin 2 → F // MvPolynomial.eval v f = 0}) ∧
  (∀ (F : Type u) [Field F] [Finite F] (f : MvPolynomial (Fin 2) F),
    Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) →
    f.degreeOf 1 = 1 →
    |(Nat.card {v : Fin 2 → F // MvPolynomial.eval v f = 0} : ℝ) -
      (Nat.card F : ℝ)| ≤ (f.degreeOf 0 : ℝ))

end Langlands.AlgebraicGeometry.LangWeil
