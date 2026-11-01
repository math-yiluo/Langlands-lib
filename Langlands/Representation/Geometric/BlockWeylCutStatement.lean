import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Representation.Geometric.BlockShapeCuts

/-! The relation between actual block-preserving permutations and interior cuts. -/

namespace Langlands.Geometric

open GeneralLinear

/-- Adjacent transpositions detect uncut edges, and block refinement reverses cut inclusion. -/
def BlockWeylCutStatement : Prop :=
  (∀ (n : ℕ) (B : BlockShape n) (i : Fin (n - 1)),
    Equiv.swap (⟨i.val, by omega⟩ : Fin n) (⟨i.val + 1, by omega⟩ : Fin n) ∈
      blockWeyl B ↔ i ∉ B.cuts) ∧
  (∀ (n : ℕ) (B K : BlockShape n),
    blockWeyl K ≤ blockWeyl B ↔ B.cuts ⊆ K.cuts)

end Langlands.Geometric
