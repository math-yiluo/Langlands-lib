import Langlands.Analysis.Meromorphic.ContinuationPrincipleReduction
import Langlands.Analysis.SeveralComplex.Hartogs.Basic

/-! # Openness, holomorphy and meromorphy in the principle of meromorphic continuation

Bernstein–Lapid, Theorem 3.3: the openness in part (1) and parts (2) and (3).
The reduction `meromorphicContinuationHolomorphic_of_hartogs` is applied to
Hartogs's theorem on separate holomorphy in diagonal form,
`Langlands.Analysis.SeveralComplex.differentiableOn_diag_of_separately`. -/

set_option autoImplicit false

universe uE uM uV uι uF

namespace Langlands.Analysis.Meromorphic

/-- The principle of meromorphic continuation (Bernstein–Lapid, Theorem 3.3):
the unique-solution locus is open, and the solution is weakly holomorphic there
and meromorphic on the ambient manifold with that locus as holomorphy domain. -/
theorem meromorphicContinuationHolomorphic :
    MeromorphicContinuationHolomorphicStatement.{uE, uM, uV, uι, uF} :=
  meromorphicContinuationHolomorphic_of_hartogs fun _ _ _ _ _ _ hU h₁ h₂ =>
    Langlands.Analysis.SeveralComplex.differentiableOn_diag_of_separately hU h₁ h₂

end Langlands.Analysis.Meromorphic
