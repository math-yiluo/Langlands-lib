import Langlands.BruhatTits.RationalPoints.CentralDerivedNormKernelCocompactnessReduction
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof
import Langlands.Representation.Plancherel.TorusNormKernelCompactnessProof
import Langlands.AlgebraicGeometry.PointTopology.SmoothOpenMapProof

/-! # Cocompactness of central and derived points in the rational norm kernel -/

universe u

namespace Langlands.BruhatTits.RationalPoints

/-- For every connected reductive group over every nonarchimedean local field, the actual
norm kernel is compact modulo its central points and the scheme-theoretic derived points. -/
theorem centralDerivedNormKernelCocompactness :
    CentralDerivedNormKernelCocompactnessStatement.{u} :=
  centralDerivedNormKernelCocompactness_of_premises
    GroupScheme.reductiveCentralTorusSurjectivity
    Plancherel.torusNormKernelCompactness
    AlgebraicGeometry.PointTopology.smoothRationalPointOpenMap

end Langlands.BruhatTits.RationalPoints
