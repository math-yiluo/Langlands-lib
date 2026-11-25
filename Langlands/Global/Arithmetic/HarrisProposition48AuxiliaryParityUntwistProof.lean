import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryParityUntwistReductionProof
import Langlands.Automorphic.HeckeDeterminantTwistWeakInductionProof
import Langlands.Automorphic.HeckeDeterminantTwistConjugateSelfDualProof
import Langlands.Automorphic.HeckeDeterminantTwistSupercuspidalProof

/-!
# Auxiliary-place determinant untwisting in Harris, Proposition 4.8

A proof of `Langlands.Global.Harris.Proposition48AuxiliaryParityUntwistStatement`: the Library's
reduction `proposition48AuxiliaryParityUntwistReduction` applied to the three determinant-twist
compatibilities of actual cuspidal realizations (`heckeDeterminantTwistWeakInduction`,
`heckeDeterminantTwistConjugateSelfDual`, `heckeDeterminantTwistSupercuspidal`, at the
number-field universe `0` fixed by the reduction). See the paired Markdown.
-/

universe uF uV

namespace Langlands.Global.Harris

open Langlands.Automorphic

/-- **Determinant untwisting at the auxiliary place.** For every parity normalization `(ν, χs)` of
a problem valid at the auxiliary place and every cuspidal class `c` solving the corrected problem,
there are actual cuspidal realizations `S`, `T` with `T` in the class `c` and `T` the twist of `S`
by `ν ∘ det`, `S` solving the raw problem (`IsUntwistedSolution`). -/
theorem proposition48AuxiliaryParityUntwist :
    Proposition48AuxiliaryParityUntwistStatement.{uF, uV} :=
  proposition48AuxiliaryParityUntwistReduction.{uF, uV} heckeDeterminantTwistWeakInduction.{0, uV}
    heckeDeterminantTwistConjugateSelfDual.{0} heckeDeterminantTwistSupercuspidal.{0, uV}

end Langlands.Global.Harris
