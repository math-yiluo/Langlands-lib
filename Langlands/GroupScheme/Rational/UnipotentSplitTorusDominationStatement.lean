import Langlands.GroupScheme.Rational.TorusDominationBaseChange
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Unipotent splitness from split-torus domination -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected affine unipotent group dominated pointedly by a split
ground-field torus has a finite normal series with one-dimensional vector
quotients over that same field. This is a proposition target, not its proof. -/
def UnipotentSplitTorusDominationStatement : Prop :=
  ∀ (k : Type u) [Field k] (U : GroupScheme (Spec (CommRingCat.of k))),
    Smooth U.X.hom → IsAffineHom U.X.hom → ConnectedSpace U.X.left →
    IsUnipotent U → HasPointedSplitTorusDomination U →
      RelativeRoot.IsSplitUnipotent U

end Langlands.GroupScheme
