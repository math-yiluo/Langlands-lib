import Langlands.Representation.Exponents.RefinedUpperSquareIntegrableConeStatement
import Langlands.Representation.Exponents.RefinedUpperSquareIntegrableCone

/-!
# Exact proof of strict upper cones for square-integrable product-Levi refinements

The published stronger cone theorem applies to the same supplied Haar measure,
representation, flattened scalar action, generalized eigencharacter and real part.
This module packages that theorem as the exact closed upper-cone statement.
-/

namespace Langlands.Exponents

universe uF uV

/-- The exact closed strict upper-cone statement, with independent field and
representation-carrier universes. -/
theorem refinedUpperSquareIntegrableCone :
    RefinedUpperSquareIntegrableConeStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n _ C
  let := T.leviTopologicalGroup C
  dsimp only
  intro _ _ μ _ V _ _ σ hsq R χ _ hgen x hx i
  exact RefinedUpperSquareIntegrableCone.isPositiveRootCone T C μ σ hsq R χ hgen x hx i

end Langlands.Exponents
