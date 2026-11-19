import Langlands.GroupScheme.Trigonalizable
import Langlands.GroupScheme.SplitSolvable
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Perfect

/-! # Split solvable groups are trigonalizable (Milne 16.52) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 16.52: let `G` be a smooth connected affine group over a field `k`.
If `G` is split solvable, then it is trigonalizable; the converse holds when `k` is perfect. -/
def SplitSolvableTrigonalizableStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (IsSplitSolvableGroupScheme G → IsTrigonalizable G) ∧
      (PerfectField k → IsTrigonalizable G → IsSplitSolvableGroupScheme G)

end Langlands.GroupScheme
