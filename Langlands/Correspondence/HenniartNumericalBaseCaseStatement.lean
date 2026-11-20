import Langlands.Correspondence.HenniartGLUpperBoundStatement
import Langlands.Correspondence.HenniartLaumonDeligneStatement

/-!
# The base case of Henniart's numerical correspondence below the ramification index

Proposition `prop:basecase` of the operator's numerical local Langlands route
note (§6.2), after Henniart (1988), Proposition 1.6 and the proposition of §5.1.
Proposition definition only.
-/

namespace Langlands.Henniart

open Langlands.Correspondence

/-- Route note, Proposition `prop:basecase`: assume (I1) and (LD). If numerical
injections over `K` exist in every rank at most `N`, then `C(K, x, N)` holds
for every real slope `x` below the absolute ramification index `e_K`. -/
def NumericalBaseCaseStatement.{uK, uW, uV} : Prop :=
  SupercuspidalStratumUpperBoundStatement.{uK, uV} →
    LaumonDeligneCountStatement.{uK, uW} →
    ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (N : ℕ),
      (∀ k : ℕ, k + 1 ≤ N → ∃ φ : IrreducibleWeilClass.{uK, uW} K k.succPNat →
          SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat,
          Numerical.IsNumericalInjection K φ) →
      ∀ x : ℝ, x < K.canonicalTopologicalData.ramificationIndex →
        Numerical.CountsAgreeUpToSlope.{uK, uW, uV} K x N

end Langlands.Henniart
