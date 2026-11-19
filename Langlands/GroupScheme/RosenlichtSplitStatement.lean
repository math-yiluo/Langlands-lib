import Langlands.GroupScheme.SplitSolvable
import Langlands.GroupScheme.Torus.Split
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Rosenlicht's criterion for split solvable groups (Milne 16.58) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Theorem 16.58 (Rosenlicht): a smooth affine solvable group `G` over a field `k`
is split solvable if there is a dominant morphism of `k`-schemes `(𝔸¹ ∖ 0)ⁿ → G`, i.e. from the
underlying scheme of the split torus `G_mⁿ`. -/
def RosenlichtSplitSolvableStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    IsSolvableGroupScheme G →
    (∃ (n : ℕ) (φ : (splitTorus (Spec (CommRingCat.of k)) (ULift.{u} (Fin n))).X ⟶ G.X),
      IsDominant φ.left) →
    IsSplitSolvableGroupScheme G

end Langlands.GroupScheme
