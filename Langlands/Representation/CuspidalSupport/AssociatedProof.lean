import Langlands.Representation.CuspidalSupport.AssociatedConditional
import Langlands.Representation.Geometric.GeometricLemmaProof
import Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof
import Langlands.Representation.Filtration.ZeroFactorDeletionProof

/-! The Weyl-transport filtration of associated cuspidal Jacquet modules. -/

namespace Langlands.CuspidalSupport

universe uF uV

/-- The actual normalized Jacquet module of quasicuspidal induction between
associated Levis is quasicuspidal and has one transport factor for every
minimal conjugating permutation, in every rank. -/
theorem associatedJacquetFiltration
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) :
    AssociatedJacquetFiltrationTheorem.{uF, uV} F T n :=
  associatedJacquetFiltration_of_prerequisites F T n
    Geometric.padicGeometricLemma
    padicAssociatedGeometricPieces
    ObjectRepFiltration.zeroFactorDeletionTheorem

end Langlands.CuspidalSupport
