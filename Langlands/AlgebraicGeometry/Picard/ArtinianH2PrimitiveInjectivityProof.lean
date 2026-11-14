import Langlands.AlgebraicGeometry.Picard.ArtinianH2PrimitiveInjectivityReduction
import Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomologyNaturalityProof
import Langlands.AbelianScheme.FieldH2ExteriorCoproductComparisonProof

/-! # Reduced-coproduct injectivity on the ideal H² of elementary Artinian thickenings -/

universe u

namespace Langlands.AbelianScheme

/-- For every elementary surjection of local Artinian rings and every abelian scheme over
the source, multiplication pullback minus the two projection pullbacks is injective on the
degree-two cohomology of the ideal sheaf of the special fibre. -/
theorem artinianH2PrimitiveInjectivity :
    ArtinianH2PrimitiveInjectivityStatement.{u} :=
  ArtinianH2PrimitiveInjectivityStatement.of_naturality
    Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology.naturalityStatement
    (fieldH2PrimitiveInjectivity_of_exteriorCoproductComparison
      fieldH2ExteriorCoproductComparison)

end Langlands.AbelianScheme
