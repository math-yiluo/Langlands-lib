import Langlands.AlgebraicGeometry.Picard.GenericAmpleFromClosedLocus
import Langlands.AlgebraicGeometry.Picard.ProperAffineFibrewiseAmpleProof
import Langlands.AlgebraicGeometry.Picard.AbelianFibreAmpleLocusClosedProof

/-! # Generic ampleness on abelian schemes over noetherian affine domains -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- On an abelian scheme over a noetherian affine integral base, a specified
line bundle whose canonical fraction-field pullback is ample is ample on the
total scheme. -/
theorem noetherianAffineAbelianGenericAmple :
    NoetherianAffineAbelianGenericAmpleStatement.{u} :=
  noetherianAffineAbelianGenericAmple_of_closedLocus
    abelianFibreAmpleLocusClosed properAffineFibrewiseAmple

end Langlands.AlgebraicGeometry.Picard
