import Langlands.Geometry.Manifold.LieGroupEllipticEstimateStatement
import Langlands.Automorphic.GroupSchemeAdaptedCasimirStatement
import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthStatement

/-! # Uniform growth of adelic automorphic forms from an elliptic estimate and a Casimir -/

universe u

namespace Langlands.Automorphic.GroupSchemeFunctions

/-- The interior estimate for elliptic left-invariant word operators on Lie groups (at the
universes of the infinite adelic points) and the adapted Casimir element together imply that
every actual adelic automorphic form has uniformly moderate growth. -/
def AdelicAutomorphicUniformGrowthReductionStatement : Prop :=
  Langlands.Geometry.Manifold.LieGroupEllipticInteriorEstimateStatement.{u, u} →
    AdelicAdaptedCasimirStatement.{u} → AdelicAutomorphicUniformGrowthStatement.{u}

end Langlands.Automorphic.GroupSchemeFunctions
