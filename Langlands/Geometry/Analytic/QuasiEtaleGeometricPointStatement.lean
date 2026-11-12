import Langlands.Geometry.Analytic.OverSitePoints

/-! # Geometric points are points of the quasi-étale site -/

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleSite

/-- For every complete algebraically closed non-Archimedean field `L` over `K`, the fibre
functor on `Qét(X)` of every `L`-valued point of an analytic space `X` satisfies the point
axioms: its category of elements is cofiltered, and covering sieves of the quasi-étale
topology are jointly surjective on its fibres. -/
def GeometricPointStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [IsAlgClosed L]
    [NormedAlgebra K L] (X : LocalizedCategory.{u, v, v} (K := K))
    (x : (localizedFieldPointFunctor L).obj X), PointAxioms L x

end Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleSite
