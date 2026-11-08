import Langlands.BruhatTits.Parabolic.FlagQuotientComparison
import Langlands.BruhatTits.Parabolic.ProperPointCompactnessAdapter
import Langlands.GroupScheme.Dynamic.FlagQuotientProof
import Langlands.AlgebraicGeometry.PointTopology.LocalFieldProperPointProofs

/-! # Compactness of actual dynamic-parabolic quotients -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.BruhatTits

/-- Both coset conventions for the actual rational points of a dynamic parabolic
are compact over every nonarchimedean local field. -/
theorem dynamicParabolicQuotientCompact :
    DynamicParabolicQuotientCompactStatement.{u} :=
  dynamicParabolicQuotientCompact_of_flag_and_proper_points
    Langlands.GroupScheme.dynamicFlagQuotientExistence.{u}
    (fun F _ _ _ _ Q hQ =>
      properSchemePointCompactness_of_localFieldProperties F
        (fun K _ _ _ _ _ hK =>
          Langlands.AlgebraicGeometry.PointTopology.localFieldProperPointProperties_proof
            K hK)
        Q hQ)

end Langlands.BruhatTits
