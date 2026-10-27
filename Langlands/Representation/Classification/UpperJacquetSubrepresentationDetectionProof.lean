import Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionStatement
import Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation
import Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof
import Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof

noncomputable section

namespace Langlands

open CuspidalJacquetMultiplicity Representation

universe uF uV uW

/-- Evaluation detects the inducing type in the actual upper Jacquet module;
the supplied ambient series supplies its positive bounded multiplicity. -/
theorem upperJacquetSubrepresentationDetection :
    UpperJacquetSubrepresentationDetectionStatement.{uF, uV, uW} := by
  intro p hp F T
  let := T.topology
  intro n B σ hσ P j hj hj0 M hM
  let := T.generalLinearTopologicalGroup n
  have hi : Function.Injective (T.normalizedJacquetMap B j) := by
    change Function.Injective (T.normalizedJacquetMap B j).toLinearMap
    rw [T.normalizedJacquetMap_toLinearMap_eq_coinvariantsMap]
    exact coinvariants_map_injective_of_smooth
      (Parabolic.unipotentFiniteContainment F T B) _ hj
      (Parabolic.isSmooth_radical F T B (induced T B σ).ρ
        (T.isSmooth_normalizedParabolicInduced B σ.ρ))
  exact jordanHolderSubobjectSimpleMapDetection ℂ (B.Levi F.Carrier)
    (upperJacquet T B (induced T B σ)) (upperJacquet T B P) σ hσ
    (T.normalizedJacquetMap B j) hi M hM
    (Or.inr (CuspidalSupport.exists_ne_zero_normalizedJacquet_hom T B j hj0))

end Langlands
