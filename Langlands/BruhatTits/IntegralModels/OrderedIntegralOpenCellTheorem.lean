import Langlands.BruhatTits.IntegralModels.OrderedIntegralOpenCellReduction
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriConnectedImageProof

/-! # Ordered integral open cells over the maximal unramified integers

The open-immersion clause of Kaletha–Prasad Proposition 8.3.14(3) over
`K = inertiaFixedField F` and `O = fixedFieldIntegers F`, obtained from the
published reduction `unramifiedOrderedIntegralOpenCellReduction` and the two
published torus theorems `unramifiedTorusConnectedBound` and
`unramifiedTorusIwahoriConnectedImage`. -/

universe u

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Proposition 8.3.14(3)**, open-immersion clause with family existence,
over the maximal unramified integers: for compatible zero data, every smooth
integral model with the specified zero-point fixer carries a torus/root model
family whose negative-root/torus/positive-root ordered integral multiplication
is an open immersion for every generic cocharacter and every pair of injective
enumerations of the indivisible roots of the two signs. -/
theorem unramifiedOrderedIntegralOpenCell :
    UnramifiedOrderedIntegralOpenCellStatement.{u} :=
  unramifiedOrderedIntegralOpenCellReduction.{u}
    unramifiedTorusConnectedBound.{u}
    unramifiedTorusIwahoriConnectedImage.{u}

end Langlands.BruhatTits.IntegralModels
