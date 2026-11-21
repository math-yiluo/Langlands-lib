import Langlands.Automorphic.GroupSchemeSliceAdelicGrowthReduction
import Langlands.Global.AdelicFiniteTranslateHeightReduction

/-!
# Slice-wise polynomial growth gives adelic moderate growth

The rational height reduction proved from the finite-translate Siegel cover closes the
published slice-to-global reduction.
-/

universe u

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global

/-- For a connected reductive group and a closed matrix representation, a continuous
rational-invariant function of finite level whose infinite slices all have polynomial growth
has moderate growth on all adelic points. -/
theorem adelicSliceModerateGrowthStatement : AdelicSliceModerateGrowthStatement.{u} :=
  adelicSliceModerateGrowthStatement_of_rationalHeightReduction
    RepresentationGrowth.adelicRationalHeightReduction_of_finiteRightSiegelCover

end Langlands.Automorphic.GroupSchemeFunctions
