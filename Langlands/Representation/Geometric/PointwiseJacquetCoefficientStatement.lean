import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Representation.CuspidalSupport.FiniteBlockShapes
import Langlands.Group.GL.ReverseBlocks

/-! Fixed-permutation cancellation for actual target-side block Weyl intersections. -/

namespace Langlands.Geometric

open scoped BigOperators

/-- The signed coefficient of each actual permutation vanishes except at the
permutation from reversed target-block coordinates to original coordinates. -/
def PointwiseJacquetCoefficientStatement : Prop := by
  classical
  exact
    ∀ (n : ℕ) (B K : GeneralLinear.BlockShape n)
        (w : Equiv.Perm (Fin n)),
      letI : Fintype (GeneralLinear.BlockShape n) :=
        Fintype.ofFinite (GeneralLinear.BlockShape n)
      Geometric.blockWeyl K ≤ Geometric.blockWeyl B →
        (∑ C : GeneralLinear.BlockShape n,
          if Geometric.IsMinimalRepresentative C B w ∧
            Geometric.blockWeyl B ⊓
              (Geometric.blockWeyl C).comap
                (MulAut.conj w⁻¹).toMonoidHom =
                  Geometric.blockWeyl K
          then (-1 : ℤ) ^ (n - C.length)
          else 0) =
        if w = B.reversePermutation
        then (-1 : ℤ) ^ (n - K.length)
        else 0

end Langlands.Geometric
