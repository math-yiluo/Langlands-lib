import Langlands.Global.Arithmetic.HarrisProposition48ParityUntwistReductionProof
import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryParityUntwistProof

/-!
# Two-place determinant untwisting in Harris, Proposition 4.8

A proof of `Langlands.Global.Harris.Proposition48ParityUntwistStatement`: the Library's reduction
`proposition48ParityUntwistReduction` applied to the auxiliary-place untwisting
`proposition48AuxiliaryParityUntwist`. See the paired Markdown.
-/

universe uF uV

namespace Langlands.Global.Harris

/-- **Determinant untwisting for the complete datum.** For every parity normalization
`(ν, χ, χs)` of a valid problem and every cuspidal class `c` solving the corrected problem, there
are actual cuspidal realizations `S`, `T` with `T` in the class `c` and `T` the twist of `S` by
`ν ∘ det`, `S` solving the raw problem (`IsUntwistedSolution`). -/
theorem proposition48ParityUntwist : Proposition48ParityUntwistStatement.{uF, uV} :=
  proposition48ParityUntwistReduction.{uF, uV} proposition48AuxiliaryParityUntwist.{uF, uV}

end Langlands.Global.Harris
