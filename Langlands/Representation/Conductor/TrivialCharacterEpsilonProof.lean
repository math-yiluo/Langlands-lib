import Langlands.Representation.Conductor.TrivialCharacterEpsilonReduction
import Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationProof

/-!
# Existence of the JPSS epsilon factor against the trivial character of `GL_1`

Over every nonarchimedean local field (any characteristic), an irreducible admissible
generic representation `π` of `GL_(n+1)(F)` has a JPSS epsilon factor against the
trivial character of `GL_1(F)`. The reduction
`trivialCharacterEpsilon_of_localFieldUnequalRankFunctionalEquation` is applied to
the published all-field unequal-rank functional equation
`RankinSelberg.localFieldUnequalRankFunctionalEquation` at carrier universes `uV`
and `0`.
-/

namespace Langlands.Conductor

universe uF uV

/-- JPSS 1983, Theorem (2.7), for `π' = 1` on `GL_1`, over every nonarchimedean
local field: the epsilon factor `ε(s, π × 1, ψ)` exists. -/
theorem trivialCharacterEpsilon : TrivialCharacterEpsilonStatement.{uF, uV} :=
  trivialCharacterEpsilon_of_localFieldUnequalRankFunctionalEquation
    RankinSelberg.localFieldUnequalRankFunctionalEquation.{uF, uV, 0}

end Langlands.Conductor
