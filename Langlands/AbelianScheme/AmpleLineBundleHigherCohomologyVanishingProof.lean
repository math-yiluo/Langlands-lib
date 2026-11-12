import Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingStatement
import Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingAssembly
import Langlands.AbelianScheme.FieldCubePullbackProof

/-! # Higher-cohomology vanishing for ample line bundles on abelian varieties over an
algebraically closed field -/

universe u

namespace Langlands.AbelianScheme

/-- On an abelian scheme over an algebraically closed field, an ample line bundle has
zero cohomology in every positive degree. -/
theorem ampleLineBundleHigherCohomologyVanishing :
    AmpleLineBundleHigherCohomologyVanishingStatement.{u} :=
  ampleLineBundleHigherCohomologyVanishing_of_cube GroupScheme.fieldCubePullback

end Langlands.AbelianScheme
