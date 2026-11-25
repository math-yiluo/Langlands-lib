import Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceProof
import Langlands.TraceFormula.TwistedGeometricSide

/-!
# Proof of the abstract simple twisted trace formula

`abstractSimpleTwistedTraceFormula` proves `AbstractSimpleTwistedTraceFormulaStatement`: the
geometric side `abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace` applied to
`abstractTwistedKernelDiagonalTrace`.

Getz–Hahn 2024, Corollary 18.5.1 (printed p. 488); Brislawn 1991, Corollary 3.2 (printed p. 237).
-/

namespace Langlands.TraceFormula

universe u

/-- **The abstract simple twisted trace formula** (`AbstractSimpleTwistedTraceFormulaStatement`):
`tr (R(f) ∘ I_θ) = ∑ i, vol((Γ ∩ C_{r i}) \ C_{r i}) · TO_{r i}(f)`. -/
theorem abstractSimpleTwistedTraceFormula : AbstractSimpleTwistedTraceFormulaStatement.{u} :=
  abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace abstractTwistedKernelDiagonalTrace

end Langlands.TraceFormula
