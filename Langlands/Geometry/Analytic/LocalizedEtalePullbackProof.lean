import Langlands.Geometry.Analytic.ConditionalLocalizedEtalePullback
import Langlands.Geometry.Analytic.FinitePiecesEtaleAllPiecesProof
import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetLocalityOfDescent
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Proof

/-! # Pullbacks along étale morphisms in the localized analytic category -/

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open AffinoidAtlasPresentation.StrongHom PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Pullbacks along étale morphisms exist in the localized analytic category,
and the base-changed projection is étale. -/
theorem localizedEtalePullbackBaseChange :
    LocalizedEtalePullbackStatement.{u, v} K :=
  localizedEtalePullback_of_targetLocality_and_finitePieces
    (finiteOverTargetLocality_of_descent finiteAffinoidAlgebraDescent)
    finitePiecesEtaleAllPieces

end Langlands.Analytic.SaturatedAtlasPresentation
