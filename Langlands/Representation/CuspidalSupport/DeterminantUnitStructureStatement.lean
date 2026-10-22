import Langlands.Representation.CuspidalSupport.DeterminantUnit
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! Structural properties of the determinant-unit subgroup of an actual product Levi. -/

namespace Langlands.CuspidalSupport

open GeneralLinear

universe uF

/-- BZ76 §3.20(a)-(b): the determinant-unit quotient is commutative,
adjoining the center gives finite index, and the central intersection is compact. -/
def LeviDeterminantUnitStructureTheorem
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n) : Prop :=
  letI := T.topology
  let G := B.Levi F.Carrier
  let H := determinantUnitSubgroup T B
  (∀ x y : G ⧸ H, x * y = y * x) ∧
    (H ⊔ Subgroup.center G).FiniteIndex ∧
    IsCompact ((H ⊓ Subgroup.center G : Subgroup G) : Set G)

end Langlands.CuspidalSupport
