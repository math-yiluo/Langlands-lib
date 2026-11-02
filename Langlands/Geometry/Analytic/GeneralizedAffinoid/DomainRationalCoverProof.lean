import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteRationalCoverFromStrictLocal
import Langlands.Geometry.Analytic.StrictTestDomain.LocalRationalNeighborhoodProof

/-! # Finite ambient rational coverage of full affinoid domains -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

/-- Every full represented affinoid domain admits a finite cover by rational
charts of its original ambient algebra, with actual bounded restrictions. -/
theorem finiteRationalCover : FiniteRationalCoverStatement.{u} :=
  finiteRationalCoverStatement_of_strictLocal
    StrictTestDomain.localRationalNeighborhood

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
