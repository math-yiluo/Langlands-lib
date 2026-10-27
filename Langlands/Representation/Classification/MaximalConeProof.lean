import Langlands.Representation.Classification.MaximalConeAssembly
import Langlands.Representation.Classification.ProductLeviDualOppositeAdapter
import Langlands.Representation.Classification.ProductLeviTemperedSufficiencyProof
import Langlands.Representation.Classification.ParabolicConeExistenceProof
import Langlands.Representation.Exponents.DualJacquetFinitenessProof
import Langlands.Representation.Parabolic.OppositeJacquetFiniteGenerationProof

/-!
# Proof of the maximal-cone selection

The published assembly `glMaximalConeJacquetQuotient_of`, applied to the published
proofs of its four hypotheses.
-/

namespace Langlands

universe uF uV

/-- Dominance-maximal selection of an essentially tempered quotient of the whole
normalized opposite Jacquet module. -/
theorem glMaximalConeJacquetQuotient : GLMaximalConeJacquetQuotientStatement.{uF, uV} :=
  glMaximalConeJacquetQuotient_of glDualJacquetFiniteness glBlockConeExists
    Parabolic.oppositeJacquetFiniteGeneration
    (glProductLeviDualOppositeTemperedSufficiency_of_core
      glProductLeviTemperedExponentSufficiency)

end Langlands
