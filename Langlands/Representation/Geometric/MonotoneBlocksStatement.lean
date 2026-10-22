import Langlands.Representation.Geometric.WeylDefinitions

/-! The consecutive positive blocks of a monotone map between finite ordinals. -/

namespace Langlands.Geometric

open GeneralLinear

/-- Every monotone map `Fin k → Fin l` is described by an actual positive
ordered block shape of `k`: the blocks of two coordinates compare exactly as
their values do. Equal values thus lie in one block and smaller values in an
earlier block. The source `k` may be zero. -/
def MonotoneBlockShapeTheorem : Prop :=
  ∀ (k l : ℕ) (f : Fin k → Fin l), Monotone f →
    ∃ S : BlockShape k, ∀ a b : Fin k, blockIndex S a ≤ blockIndex S b ↔ f a ≤ f b

end Langlands.Geometric
