import Langlands.GroupScheme.Lie.AffineBracket
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.Algebra.Lie.Nilpotent

/-! # Unipotence via the full centre and the nilpotent tangent Lie algebra -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Lie

/-- Milne 16.61(a,b): for a smooth connected affine group over a field, unipotence
is equivalent to unipotence of the full centre and Lie-algebra nilpotence. -/
def UnipotentNilpotentLieCenterStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (Z : GroupScheme (Spec (CommRingCat.of k))) (z : Z ⟶ G),
    IsClosedSubgroup z → (center G).IsRepresentedBy z →
      letI := instAffineKernelLieRing (R := CommRingCat.of k) (A := CommRingCat.of k) G
      IsUnipotent G ↔
        IsUnipotent Z ∧ LieRing.IsNilpotent (Additive (lieKernel G (CommRingCat.of k)))

end Langlands.GroupScheme.Lie
