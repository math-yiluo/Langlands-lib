import Langlands.GroupScheme.Rational.SemigroupSmoothQuotientReduction
import Langlands.GroupScheme.Rational.SemigroupFunctorialityReduction
import Langlands.GroupScheme.Rational.SemigroupRealizationProof
import Langlands.GroupScheme.Rational.CoordinateSemigroupProof
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.GroupScheme.Lie.SurjectiveDifferentialProof

/-! # Smooth quotients of the actual semigroup subgroup functors -/

universe u

namespace Langlands.GroupScheme.RelativeRoot

/-- A smooth equivariant surjection induces a smooth scheme surjection between
every pair of representatives of the actual semigroup subgroup functors. -/
theorem semigroupSmoothQuotient : SemigroupSmoothQuotientStatement.{u} :=
  semigroupSmoothQuotient_of_realization_functoriality_differential
    semigroupRealization
    (semigroupFunctoriality_of_imageGeneration_and_containment
      ImageGeneration.pointedImageGeneration
      CoordinateWeights.coordinateSemigroupComparison.2)
    Lie.smoothSurjectiveOfSurjectiveDifferential

end Langlands.GroupScheme.RelativeRoot
