import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetLocalityOfDescent
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.Proof

/-! # Target-local finiteness criterion -/

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

/-- Target-local finiteness for actual saturated analytic presentations. -/
theorem finiteOverTargetLocality (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] :
    FiniteOverTargetLocalityStatement.{u, v, w} K :=
  finiteOverTargetLocality_of_descent
    PresentedAffinoidAlgebra.finiteAffinoidAlgebraDescent.{u}

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
