import Langlands.Representation.Plancherel.RationalUnramifiedComplexTorusStatement
import Langlands.Representation.Plancherel.RationalUnramifiedBasisChartIndependenceProof
import Langlands.Representation.Plancherel.RationalUnramifiedComplexLieGroupProof
import Langlands.Representation.Plancherel.RationalUnramifiedComplexExponentialProof
import Langlands.Representation.Plancherel.RationalUnitaryUnramifiedSubmanifoldProof

/-! # The complex torus `X(G)` and its real subtorus `Im X(G)` (Renard V.3.20): proof

The conjunction `RationalUnramifiedComplexTorusStatement` is assembled from the four published
component proofs. -/

set_option autoImplicit false

namespace Langlands.Plancherel

universe u

/-- Renard V.3.20, smooth structure of `X(G)` and `Im X(G)`: the four published component
proofs, paired in the order of `RationalUnramifiedComplexTorusStatement`. -/
theorem rationalUnramifiedComplexTorus : RationalUnramifiedComplexTorusStatement.{u} :=
  ⟨rationalUnramifiedBasisChartIndependence, rationalUnramifiedComplexLieGroup,
    rationalUnramifiedComplexExponential, rationalUnitaryUnramifiedSubmanifold⟩

end Langlands.Plancherel
