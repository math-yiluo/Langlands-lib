import Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
import Langlands.Representation.Classification.Segments

/-! Conditional self-tensor multiplicity one for actual segment inductions. -/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData CuspidalJacquetMultiplicity

universe uF uV

/-- The full cuspidal Jacquet count theorem implies self-tensor multiplicity
one for both Jacquet directions of both orders of segment induction. -/
def SegmentJacquetMultiplicityReductionStatement
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  GLCuspidalJacquetMultiplicityStatement.{uF,uV,uV} →
    letI := T.topology
    ∀ {r : ℕ} (m : ℕ) (_hm : 0 < m) (hr : 0 < r)
      (A : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r)),
      let B := BlockShape.uniform m r hr
      let σ := FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)
      let τ := FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj m hr)
      let Iu := Rep.of (T.segmentInduced A.obj m hr).representation
      let Id := Rep.of (T.segmentInducedDown A.obj m hr).representation
      HasJordanHolderMultiplicity (upperJacquet T B Iu) σ.obj 1 ∧
      HasJordanHolderMultiplicity (oppositeJacquet T B Iu) σ.obj 1 ∧
      HasJordanHolderMultiplicity (upperJacquet T B Id) τ.obj 1 ∧
      HasJordanHolderMultiplicity (oppositeJacquet T B Id) τ.obj 1

end Langlands.Classification
