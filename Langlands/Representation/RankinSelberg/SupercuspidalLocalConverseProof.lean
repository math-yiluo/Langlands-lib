import Langlands.Representation.RankinSelberg.LocalConverseStatement
import Langlands.Representation.RankinSelberg.SupercuspidalGraphReduction
import Langlands.Representation.RankinSelberg.SupercuspidalProductCompletenessProof

/-!
# Henniart's supercuspidal local converse theorem

Two irreducible supercuspidal representations of `GL_n(F)`, `n ≥ 2`, over a p-adic field with
the same epsilon factors of pairs against every irreducible supercuspidal representation of
`GL_r(F)`, `1 ≤ r ≤ n - 1`, are equivalent (Henniart 1993, Corollary, printed page 340).
-/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- Henniart's supercuspidal local converse theorem for epsilon factors of pairs. -/
theorem supercuspidalLocalConverse : SupercuspidalLocalConverseStatement.{uF, uV, uW} :=
  supercuspidalLocalConverse_of_completeness supercuspidalProductCompleteness.{uF, uW}

end Langlands.RankinSelberg
