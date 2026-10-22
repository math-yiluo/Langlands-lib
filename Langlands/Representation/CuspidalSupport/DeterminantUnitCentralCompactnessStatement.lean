import Langlands.Representation.CuspidalSupport.DeterminantUnit

/-! Compactness of the determinant-unit subgroup's intersection with the Levi center. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF

/-- BZ76 §3.20(a): the determinant-unit intersection with the actual Levi center is compact. -/
def LeviDeterminantUnitCentralCompactnessTheorem
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) : Prop :=
  letI := T.topology
  IsCompact
    (((determinantUnitSubgroup T B) ⊓ Subgroup.center (B.Levi F.Carrier) :
      Subgroup (B.Levi F.Carrier)) : Set (B.Levi F.Carrier))

end Langlands.CuspidalSupport
