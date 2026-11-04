import Langlands.GroupScheme.Reductive.UnipotentRadical
import Langlands.GroupScheme.Rational.AffineLineRigidity

/-! # Woundness of the ordinary radical modulo the split radical -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Supplied fppf quotients of the ordinary ground-field unipotent radical
by the split ground-field unipotent radical have only constant affine-line
maps. This is an all-field proposition target, with no existence claim. -/
def SplitRadicalWoundQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    ∀ (U V : GroupScheme (Spec (CommRingCat.of k)))
      (j : U ⟶ G) (n : V ⟶ G),
      IsUnipotentRadical j → IsSplitUnipotentRadical n →
      ∀ m : V ⟶ U, m ≫ j = n →
        ∀ (Q : GroupScheme (Spec (CommRingCat.of k)))
          [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
          (q : U ⟶ Q),
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range m) q →
            HasConstantAffineLineMaps Q

end Langlands.GroupScheme
