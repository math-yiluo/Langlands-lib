import Langlands.GroupScheme.Reductive.DerivedTorusParabolicCentralProductReduction
import Langlands.GroupScheme.Reductive.DerivedCentralIsogenyProof

/-! # Maximal tori and parabolic subgroups of a reductive group and its derived group -/

universe u

namespace Langlands.GroupScheme

/-- Intersection with the derived group gives the maximal-torus and parabolic
correspondences, with inverse given by multiplication with the maximal central torus. -/
theorem reductiveDerivedTorusParabolicCorrespondence :
    ReductiveDerivedTorusParabolicCorrespondenceStatement.{u} :=
  reductiveDerivedTorusParabolicCentralProductReduction
    reductiveDerivedCentralIsogeny

end Langlands.GroupScheme
