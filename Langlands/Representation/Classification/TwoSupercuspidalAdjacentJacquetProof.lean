import Langlands.Representation.Classification.TwoSupercuspidalAdjacentStructure
import Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
import Langlands.Representation.CuspidalSupport.AssociatedProof

/-! The actual ordered Jacquet factors of every proper adjacent product subspace. -/

namespace Langlands.Classification

universe uF uV

/-- Every nonzero proper subrepresentation of an adjacent two-supercuspidal
product has normalized Jacquet module equivalent to the ordered inducing
tensor, and its quotient has the reversed tensor as normalized Jacquet module. -/
theorem twoSupercuspidalAdjacentProductJacquet
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSupercuspidalAdjacentProductJacquet.{uF, uV} F T := by
  let := T.topology
  intro k hk ρ ρ' h
  exact (TwoSupercuspidalAdjacent.adjacentStructure F T hk
    (CuspidalSupport.nonassociatedJacquetSubquotients F T (k + k))
    (CuspidalSupport.associatedJacquetFiltration F T (k + k)) ρ ρ' h).2

end Langlands.Classification
