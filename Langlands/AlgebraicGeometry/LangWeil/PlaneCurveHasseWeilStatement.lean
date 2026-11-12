import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The Hasse–Weil bound for absolutely irreducible plane curves (Schmidt)

W. M. Schmidt's elementary form of the Riemann hypothesis for plane curves over finite fields,
obtained by Stepanov's method: an absolutely irreducible polynomial `f(X, Y)` over `𝔽_q` of
degree `m > 0` in `X` and `n > 0` in `Y` has `q + O(q^{1/2})` zeros in `𝔽_q²` once `q` is large
compared with `m` and `n`.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- Schmidt's theorem (*Zur Methode von Stepanov*, Acta Arith. 24 (1973), Satz, printed
p.347). Let `F` be a finite field with `q` elements and `f ∈ F[X, Y]` absolutely irreducible
(irreducible over an algebraic closure of `F`), of degree `m > 0` in `X` and `n > 0` in `Y`.
If `q > 9 (m + 1)² (n + 1)²`, then the number `A` of `(x, y) ∈ F²` with `f(x, y) = 0` satisfies
`|A - q| < 2 min(m² n, n² m) q^{1/2}`. The variables `X` and `Y` are `X 0` and `X 1`. -/
def PlaneCurveHasseWeilStatement : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (f : MvPolynomial (Fin 2) F),
    Irreducible (MvPolynomial.map (algebraMap F (AlgebraicClosure F)) f) →
    0 < f.degreeOf 0 → 0 < f.degreeOf 1 →
    9 * (f.degreeOf 0 + 1) ^ 2 * (f.degreeOf 1 + 1) ^ 2 < Nat.card F →
    |(Nat.card {v : Fin 2 → F // MvPolynomial.eval v f = 0} : ℝ) - (Nat.card F : ℝ)| <
      2 * (min (f.degreeOf 0 ^ 2 * f.degreeOf 1) (f.degreeOf 1 ^ 2 * f.degreeOf 0) : ℕ) *
        Real.sqrt (Nat.card F)

end Langlands.AlgebraicGeometry.LangWeil
