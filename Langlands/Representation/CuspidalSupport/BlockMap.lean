import Langlands.Representation.Geometric.WeylDefinitions

/-! The common block-label map of a coordinate permutation. -/

namespace Langlands.CuspidalSupport

open GeneralLinear Geometric

/-- The target block containing the image of the first coordinate of a source block. -/
def blockMap {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (i : Fin B.length) : Fin C.length :=
  blockIndex C (w (B.index i ⟨0, B.positive i⟩))

end Langlands.CuspidalSupport
