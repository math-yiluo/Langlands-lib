import Langlands.Geometry.Analytic.FinitePiecesEtaleAllPiecesReduction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFlatnessProof
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof

/-! # Pointwise étaleness from finite to arbitrary recognized pieces -/

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Joint pointwise étaleness on a finite neighborhood family implies the
all-pieces condition for the actual strong map. -/
theorem finitePiecesEtaleAllPieces :
    FinitePiecesEtaleAllPiecesStatement.{u, v, w} K :=
  finitePiecesEtaleAllPieces_of_flatness_tensor
    PresentedAffinoidAlgebra.Domain.flatness
    (PresentedAffinoidAlgebra.AffinoidPushout.finiteTensorComparison (K := K))

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
