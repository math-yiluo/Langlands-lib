import Langlands.Representation.Exponents.Chambers
import Langlands.Group.GL.ReverseBlocks
import Langlands.Representation.Geometric.WeylDefinitions

/-! Coarse projection rigidity in the raw reversed upper-geometric indexing. -/

namespace Langlands.Exponents

open GeneralLinear Geometric
open scoped BigOperators

/-- The leading coarse projection can occur only at the inverse block reversal
among the raw upper-geometric minimal representatives. -/
def ReversedCoarseProjectionWeylRigidityStatement : Prop :=
  ∀ (n : ℕ) (B : BlockShape n)
    (t : Fin B.length → ℝ) (v : Equiv.Perm (Fin n)) (x : Fin n → ℝ),
    StrictAnti t →
    IsMinimalRepresentative B B.reverse v →
    (∀ i : Fin B.length,
      IsClosedPositiveRootCone (fun a : Fin (B.size i) => x (B.index i a))) →
    (∀ i : Fin B.length,
      (∑ a : Fin (B.size i),
        (x ((B.reversePermutation * v).symm (B.index i a)) +
          t (blockIndex B ((B.reversePermutation * v).symm (B.index i a))))) =
        (B.size i : ℝ) * t i) →
    v = B.reversePermutation.symm

end Langlands.Exponents
