import Langlands.Representation.Archimedean.RealJacquetFiniteGenerationProof
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof
import Langlands.Representation.Archimedean.RealJacquetNonvanishingProof
import Langlands.Representation.Archimedean.RealPrincipalSeriesSubquotientProof

/-!
# Casselman's subrepresentation theorem for `GL_n(ℝ)`

Proof of `Langlands.Archimedean.RealPrincipalSeriesSubrepresentationStatement`. It combines
finite generation over `U(𝔫)`, the nonvanishing of the Jacquet module (from the subquotient
theorem) and the Frobenius embedding.
-/

noncomputable section

namespace Langlands.Archimedean

namespace RealPrincipalSeriesSubrepresentation

universe uV

/-- Casselman's subrepresentation theorem, given nonvanishing of the Jacquet module. -/
theorem of_nonvanishing (hnv : RealJacquetNonvanishingStatement.{uV}) :
    RealPrincipalSeriesSubrepresentationStatement.{uV} :=
  realPrincipalSeriesSubrepresentationJacquetReduction
    (realJacquetModuleFinite_of_finiteDimensional_of_nonvanishing
      (realJacquetFiniteDimensional_of_finiteGeneration
        RealJacquetFiniteGeneration.realJacquetFiniteGeneration) hnv)
    RealJacquetFrobenius.realJacquetFrobenius

end RealPrincipalSeriesSubrepresentation

universe uV

/-- **Casselman's subrepresentation theorem for `GL_n(ℝ)`.** Every irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module embeds into the `O(n)`-finite vectors of a principal series. -/
theorem realPrincipalSeriesSubrepresentation :
    RealPrincipalSeriesSubrepresentationStatement.{uV} :=
  RealPrincipalSeriesSubrepresentation.of_nonvanishing
    (RealJacquetNonvanishing.realJacquetNonvanishingSubquotientReduction
      realPrincipalSeriesSubquotient)

end Langlands.Archimedean
