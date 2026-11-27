import Langlands.Automorphic.Unramified.RestrictedCyclicBaseChangeComplexPlaceCompatibilityStatement
import Langlands.Automorphic.Unramified.RestrictedCyclicWeakBaseChangeComplexPlaceStatement

/-!
# Restricted B7 from the restricted complex-place compatibility

One implication: the restricted complex-place compatibility
`RestrictedCyclicBaseChangeComplexPlaceCompatibilityStatement`, at the universe levels of the
conclusion, implies restricted B7, `RestrictedCyclicWeakBaseChangeComplexPlaceStatement`.
A statement only; see the paired Markdown.
-/

universe uF uE uV uW

namespace Langlands.Automorphic.Unramified

/-- Restricted B7 from the restricted complex-place compatibility at the same universe levels:
fields `F` in `uF` and `E` in `uE`, spectral presentations over `F` in `uV` and over `E` in
`uW`. -/
def RestrictedCyclicWeakBaseChangeComplexPlaceReductionStatement : Prop :=
  RestrictedCyclicBaseChangeComplexPlaceCompatibilityStatement.{uF, uE, uV, uW} →
    RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{uF, uE, uV, uW}

end Langlands.Automorphic.Unramified
