import Langlands.Representation.Classification.Supercuspidal
import Langlands.Representation.Category.Subquotients
import Langlands.Representation.Jacquet.Parabolic
import Langlands.Representation.Tensor.Finite

/-! Actual cuspidal tensor quotients of normalized upper Jacquet modules. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (T : F.TopologicalData)

/-- Every positive-rank irreducible smooth representation has an actual
supercuspidal external tensor quotient of one normalized upper Jacquet module. -/
def CuspidalTensorJacquetQuotientExistence : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n →
    ∀ π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier),
      π.IsIrreducible →
      ∃ (B : BlockShape n)
        (C : ∀ i : Fin B.length,
          SupercuspidalRep.{uF, max uF uV} (F := F.Carrier) (n := B.size i)),
        SmoothRep.IsQuotient
          (FiniteTensor.externalSmoothObject (fun i => (C i).obj))
          ((T.normalizedJacquetFunctor B).obj π)

end Langlands.CuspidalSupport
