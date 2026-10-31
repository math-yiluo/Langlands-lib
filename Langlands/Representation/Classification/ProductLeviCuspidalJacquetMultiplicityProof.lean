import Langlands.Representation.Classification.ProductLeviCuspidalJacquetAssembly
import Langlands.Representation.Parabolic.RefinedInductionTensorProof
import Langlands.Representation.CuspidalSupport.AssociatedProof
import Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof

/-! Opposite cuspidal Jacquet length and multiplicities inside a product Levi. -/

namespace Langlands

universe uF uV uW

/-- The opposite self-Jacquet module of the refined induction of an irreducible cuspidal
representation of the fine Levi has length the number of minimal self-conjugating
permutations in the coarse block Weyl group, and every irreducible representation
occurs with multiplicity the number of associating permutations in that group. -/
theorem productLeviCuspidalJacquetMultiplicity :
    ProductLeviCuspidalJacquetMultiplicityStatement.{uF, uV, uW} :=
  productLeviCuspidalJacquetMultiplicity_of_upstream Parabolic.refinedInductionTensor
    (fun _ _ F T n _ => CuspidalSupport.associatedJacquetFiltration F T n)
    glOppositeCuspidalJacquetFiltrationFromUpper

end Langlands
