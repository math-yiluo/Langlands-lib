import Langlands.Geometry.Analytic.QuasiEtaleGeometricPointCones
import Langlands.Geometry.Analytic.QuasiEtaleSiteFieldPointLift

/-! # Geometric points of the quasi-étale site -/

universe u v uL

namespace Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleSite

/-- The fibre functor of a geometric point satisfies the point axioms of the
quasi-étale site. -/
theorem geometricPoint : GeometricPointStatement.{u, v, uL} :=
  geometricPointStatement_of_geometry
    ⟨geometricPointRefinement, geometricPointEqualization, geometricPointImageLift⟩

end Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleSite
