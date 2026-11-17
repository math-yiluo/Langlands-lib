import Langlands.GroupScheme.Rational.SplitSolvableBorelConnected
import Langlands.GroupScheme.Rational.SplitSolvableBorelConjugacyReduction

/-! # Proof: split Borel subgroups over an arbitrary field (Milne 17.105(a),(b)) -/

universe u

namespace Langlands.GroupScheme

/-- Milne, Theorem 17.105(a),(b): split solvable subgroups lie in a rational conjugate of a split
Borel subgroup, and split Borel subgroups are rationally conjugate. -/
theorem splitSolvableBorelConjugacy : SplitSolvableBorelConjugacyStatement.{u} :=
  SplitSolvableBorelConjugacy.splitSolvableBorelConjugacy_of_connected
    splitSolvable_borel_containment_connected

end Langlands.GroupScheme
