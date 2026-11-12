import Langlands.AlgebraicGeometry.PointTopology.HenselianIffSeparablyClosedProof
import Langlands.AlgebraicGeometry.PointTopology.HenselianValuationRingProof
import Langlands.AlgebraicGeometry.PointTopology.TensorCompletionProductProof
import Langlands.AlgebraicGeometry.PointTopology.HenselianTensorCompletionFieldProof
import Langlands.AlgebraicGeometry.PointTopology.HenselianArchimedeanProof
import Langlands.AlgebraicGeometry.PointTopology.HenselianFiniteEtaleEquivalenceProof

/-!
# The henselian valued field facts of Conrad's printed p.14

This module assembles the six proved assertions into the conjunction
`HenselianValuedFieldPropertiesStatement`.
-/

universe u

namespace Langlands.AlgebraicGeometry.PointTopology

/-- **Conrad's p.14 facts on henselian valued fields.** -/
theorem henselianValuedFieldProperties : HenselianValuedFieldPropertiesStatement.{u} :=
  ⟨henselianIffSeparablyClosed, henselianIffValuationRingHenselian, tensorCompletionProduct,
    henselianTensorCompletionField, archimedeanHenselian, henselianFiniteEtaleEquivalence⟩

end Langlands.AlgebraicGeometry.PointTopology
