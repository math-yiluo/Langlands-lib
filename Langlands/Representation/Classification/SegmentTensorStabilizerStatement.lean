import Langlands.Representation.Classification.Segments
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Tensor.Finite

/-! Stabilizer counts and cuspidality for the actual segment Levi tensors. -/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData CuspidalSupport

universe uF uV

/-- Actual increasing and decreasing segment tensors have a unique minimal
self-association and, in positive length, are irreducible cuspidal Levi objects. -/
def SegmentTensorStabilizerAndCuspidality
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ {r : ℕ} (m : ℕ) (hr : 0 < r)
    (A : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r)),
    let B := BlockShape.uniform m r hr
    let σ := FiniteTensor.externalSmoothObject (T.segmentFactors A.obj m hr)
    let τ := FiniteTensor.externalSmoothObject (T.segmentFactorsDown A.obj m hr)
    Nat.card (AssociatingPermutations B B σ.representation σ.representation) = 1 ∧
    Nat.card (AssociatingPermutations B B τ.representation τ.representation) = 1 ∧
    (0 < m →
      (σ.IsIrreducible ∧ IsLeviCuspidal B σ.representation) ∧
      (τ.IsIrreducible ∧ IsLeviCuspidal B τ.representation))

end Langlands.Classification
