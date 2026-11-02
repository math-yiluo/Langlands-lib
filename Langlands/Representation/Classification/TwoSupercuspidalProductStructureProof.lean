import Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement
import Langlands.Representation.Classification.TwoSupercuspidalAdjacentStructure
import Langlands.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof
import Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof
import Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
import Langlands.Representation.CuspidalSupport.AssociatedProof

/-!
# The product of two supercuspidal representations (Ze80 1.11)

Zelevinsky 1980, Proposition 1.11, assembled from the published nonadjacent
irreducibility, adjacent reducibility, the two Jacquet-of-induction theorems
and the algebraic part of (b) in `TwoSupercuspidalAdjacentStructure`.
-/

namespace Langlands.Classification

universe uF uV

/-- Zelevinsky 1980, Proposition 1.11: nonadjacent products of two
supercuspidal representations are irreducible, and an adjacent product has
length two, a unique nonzero proper invariant subspace, irreducible
subrepresentation and quotient, and the ordered normalized Jacquet modules
`ρ ⊗ ρ'` and `ρ' ⊗ ρ`. -/
theorem twoSupercuspidalProductStructure
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSupercuspidalProductStructure.{uF, uV} F T :=
  TwoSupercuspidalAdjacent.productStructure_of F T
    (twoSupercuspidalNonadjacentProductIrreducible F T)
    (twoSupercuspidalAdjacentProductReducible F T)
    (fun n => CuspidalSupport.nonassociatedJacquetSubquotients F T n)
    (fun n => CuspidalSupport.associatedJacquetFiltration F T n)

end Langlands.Classification
