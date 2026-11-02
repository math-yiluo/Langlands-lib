import Langlands.Representation.Classification.SegmentFullJacquetStatement
import Langlands.Representation.Classification.SegmentFullJacquetEdgeData
import Langlands.Representation.Classification.TwoSupercuspidalProductStructureProof
import Langlands.Representation.Geometric.GeometricLemmaProof
import Langlands.Representation.CuspidalSupport.AssociatedProof

/-!
# Full cuspidal Jacquet modules of segment subrepresentations and quotients

Zelevinsky 1980, 3.1 and 9.1(*), assembled from the published conditional
assembly `segmentFullJacquetFormula_of_prerequisites`, the associated Jacquet
filtration, the geometric lemma and Ze80 1.11.
-/

namespace Langlands.Classification

universe uF uV

/-- Zelevinsky 1980, 3.1 and 9.1(*): the normalized Jacquet module along
`(r, …, r)` of an irreducible subrepresentation of `A × νA × … × ν^(m-1)A` is
equivalent to `A ⊗ νA ⊗ … ⊗ ν^(m-1)A`, and that of an irreducible quotient to
`ν^(m-1)A ⊗ … ⊗ νA ⊗ A`. -/
theorem segmentFullJacquetFormula
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentFullJacquetFormula.{uF, uV} F T :=
  SegmentFullJacquet.segmentFullJacquetFormula_of_prerequisites F T
    (fun n => CuspidalSupport.associatedJacquetFiltration F T n)
    Geometric.padicGeometricLemma.{uF, uV}
    Geometric.padicGeometricLemma.{uF, max uF uV}
    (twoSupercuspidalProductStructure F T)

end Langlands.Classification
