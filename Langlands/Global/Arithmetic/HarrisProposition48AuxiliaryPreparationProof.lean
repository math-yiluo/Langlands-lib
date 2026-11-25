import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryRankOneProof
import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryParityNormalizationProof
import Langlands.Global.Arithmetic.HarrisProposition48AuxiliaryParityUntwistProof

/-!
# The one-place preparation for Harris, Proposition 4.8

A proof of `Langlands.Global.Harris.Proposition48AuxiliaryPreparationStatement`, the conjunction
of the rank-one base case and the two auxiliary-place parity statements:
`proposition48AuxiliaryRankOne`, `proposition48AuxiliaryParityNormalization` and
`proposition48AuxiliaryParityUntwist`. See the paired Markdown.
-/

universe uF uV

namespace Langlands.Global.Harris

/-- **The one-place preparation.** The rank-one base case, the auxiliary-place parity
normalization and the auxiliary-place determinant untwisting of the internal induction for
Harris, Proposition 4.8. -/
theorem proposition48AuxiliaryPreparation :
    Proposition48AuxiliaryPreparationStatement.{uF, uV} :=
  ⟨proposition48AuxiliaryRankOne.{uF, uV}, proposition48AuxiliaryParityNormalization.{uF},
    proposition48AuxiliaryParityUntwist.{uF, uV}⟩

end Langlands.Global.Harris
