import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Group.GL.ReverseBlocks

/-! # Reversing the inner blocks of a refinement -/

namespace Langlands.ProductLeviDualOpposite

open GeneralLinear Geometric

universe u

variable {n : ℕ} (C : BlockShape n) (D : BlockRefinement C)

/-- Reverse the order of the inner blocks in every outer block. -/
def reverseRefinement : BlockRefinement C := fun j => (D j).reverse

@[simp] theorem reverseRefinement_apply (j : Fin C.length) :
    reverseRefinement C D j = (D j).reverse := rfl

variable (R : Type u) [CommRing R]

/-- The blockwise reversal matrices in the outer product Levi. -/
def reverseWeyl : C.Levi R := fun j => (D j).reverseMatrix R

end Langlands.ProductLeviDualOpposite
