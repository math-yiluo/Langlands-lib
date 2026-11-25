import Langlands.Global.Arithmetic.HarrisProposition48ParityNormalizationProof
import Langlands.Global.Arithmetic.HarrisProposition48ParityUntwistProof

/-!
# The two-place parity transport for Harris, Proposition 4.8

A proof of `Langlands.Global.Harris.Proposition48ParityTransportStatement`, the conjunction of
the two-place parity normalization `proposition48ParityNormalization` and the two-place
determinant untwisting `proposition48ParityUntwist`. See the paired Markdown.
-/

universe uF uV

namespace Langlands.Global.Harris

/-- **The two-place parity transport.** Parity normalization and determinant untwisting for the
complete Proposition 4.8 datum. -/
theorem proposition48ParityTransport : Proposition48ParityTransportStatement.{uF, uV} :=
  ⟨proposition48ParityNormalization.{uF}, proposition48ParityUntwist.{uF, uV}⟩

end Langlands.Global.Harris
