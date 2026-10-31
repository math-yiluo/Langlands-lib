import Langlands.Representation.Exponents.InducedCuspidalExponentPersistenceConditional
import Langlands.Representation.Geometric.GeometricLemmaProof

/-! Persistence of cuspidal exponents of real-twisted inductions. -/

noncomputable section

namespace Langlands

universe uF uV uW uM

/-- One actual geometric-filtration label identifies the twisted cuspidal
exponent and occurs at the untwisted parameter. -/
theorem glInducedCuspidalExponentPersistence :
    GLInducedCuspidalExponentPersistenceStatement.{uF, uV, uW, uM} := by
  exact InducedCuspidalExponentPersistence.persistence_of_geometricLemmas.{uF, uV, uW, uM}
    Geometric.padicGeometricLemma.{uF, uW}
    Geometric.padicGeometricLemma.{uF, uV}

end Langlands
