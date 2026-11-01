import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackIdentityProof
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackCompositionProof
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackCoefficientNaturalityProof
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackDegreeZeroProof
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackSplitRetractionProof

/-!
# The five laws of canonical pullback on actual relative cohomology
-/

universe u

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- The actual canonical pullback satisfies identity, composition,
coefficient naturality, degree-zero normalization, and split retraction. -/
theorem relativeCohomologyPullbackLawsStatement :
    RelativeCohomologyPullbackLawsStatement.{u} :=
  ⟨relativeCohomologyPullbackIdentityStatement,
    relativeCohomologyPullbackCompositionStatement,
    relativeCohomologyPullbackCoefficientNaturalityStatement,
    relativeCohomologyPullbackDegreeZeroStatement,
    relativeCohomologyPullbackSplitRetractionStatement⟩

end Langlands.AlgebraicGeometry.Modules.DerivedSections
