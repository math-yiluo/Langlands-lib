import Langlands.Representation.Classification.Segments
import Langlands.Representation.CuspidalSupport.LeviDefinitions
import Langlands.Representation.Tensor.Finite

/-! The self-stabilizer count for distinct actual cuspidal tensor factors. -/

namespace Langlands.CuspidalSupport

open GeneralLinear PadicField.TopologicalData

universe uF uV

/-- Distinct cuspidal block data leave exactly one minimal coordinate
permutation associating their external tensor to itself. -/
def GLDistinctCuspidalTensorStabilizerStatement
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ {n : ℕ} (B : BlockShape n)
    (A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)),
    Function.Injective (fun i =>
      (⟨B.size i, B.positive i, (A i).isoClass⟩ : CuspidalDatum.{uV,uF} T)) →
    Nat.card (AssociatingPermutations B B
      (FiniteTensor.external (fun i => (A i).obj.representation))
      (FiniteTensor.external (fun i => (A i).obj.representation))) = 1

end Langlands.CuspidalSupport
