import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChangeStatement
import Langlands.AlgebraicGeometry.RelativeDifferentialsBaseChangeProof
import Langlands.AlgebraicGeometry.RelativeDifferentialsAffineBaseChangeProof
import Langlands.AlgebraicGeometry.RelativeDifferentialsOpenImmersionProof

/-! # Arbitrary base change for the canonical relative differential sheaf map -/

noncomputable section

universe u

namespace Langlands.Scheme

/-- The canonical relative differential sheaf map is invertible under arbitrary base change. -/
theorem relativeDifferentialsBaseChangeIsIso (S : AlgebraicGeometry.Scheme.{u}) :
    RelativeDifferentialsBaseChangeIsIsoStatement S :=
  relativeDifferentialsBaseChangeIsIso_of_local_inputs
    relativeDifferentialsOpenImmersionIsIso relativeDifferentialsAffineBaseChangeIsIso S

end Langlands.Scheme
