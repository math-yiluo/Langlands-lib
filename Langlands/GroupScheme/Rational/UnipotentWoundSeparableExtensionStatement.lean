import Langlands.GroupScheme.Rational.AffineLineRigidity
import Mathlib.FieldTheory.Separable

/-! # Woundness under separable algebraic field extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Affine-line constancy of a smooth connected affine unipotent group is
invariant under arbitrary separable algebraic field extension. This is an
all-characteristic proposition target, not a proof of invariance. -/
def UnipotentWoundSeparableExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsUnipotent G →
      (HasConstantAffineLineMaps G ↔
        HasConstantAffineLineMaps
          ((GroupScheme.baseChange
            (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G))

end Langlands.GroupScheme
