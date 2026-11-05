import Langlands.GroupScheme.Reductive.CentralTorusQuotientFiniteReduction
import Langlands.GroupScheme.Rational.SplitTorusKernelCentralityProof
import Langlands.GroupScheme.Rational.SplitTorusIsogenyOfLatticeMapsProof
import Langlands.GroupScheme.CentralIsogeny.MaximalTorusImageProof

/-! # The split central torus quotient -/

universe u

namespace Langlands.GroupScheme

/-- The quotient of a connected reductive group with split maximal torus `T` by the kernel
of a torus map `t : T ⟶ T'` whose character group contains the roots. -/
theorem splitCentralTorusQuotient : SplitCentralTorusQuotientStatement.{u} :=
  splitCentralTorusQuotient_of_prerequisites' splitTorusKernelCentrality
    splitTorusIsogenyOfLatticeMaps centralIsogenyMaximalTorusImage

end Langlands.GroupScheme
