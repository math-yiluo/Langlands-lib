import Langlands.GroupScheme.Rational.AffineLineRigidity
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.FieldTheory.Perfect

/-! # Wound unipotent groups over perfect fields (Milne 14.70) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, 14.70 with Definition 14.69: over a perfect field `k`, a connected unipotent
group variety `G` is wound (`HasConstantAffineLineMaps G`: every morphism of `k`-schemes from
the affine line to `G` is constant with value a `k`-point) if and only if `G` is finite. -/
def PerfectFieldWoundUnipotentFiniteStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ConnectedSpace G.X.left → IsUnipotent G →
      (HasConstantAffineLineMaps G ↔ IsFinite G.X.hom)

end Langlands.GroupScheme
