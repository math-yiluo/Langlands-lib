import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.VectorGroupQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.Perfect

/-! # Central additive subgroups of unipotent groups over perfect fields (Milne 14.55) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 14.55: over a perfect field `k` of characteristic `p > 0`, every
nontrivial smooth connected affine unipotent group `U` has a central closed subgroup isomorphic
to the additive group `𝔾ₐ = VectorGroup.groupScheme k 1`. -/
def PerfectFieldCentralAdditiveSubgroupStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (U : GroupScheme (Spec (CommRingCat.of k))) [Smooth U.X.hom] [IsAffineHom U.X.hom],
    ConnectedSpace U.X.left → IsUnipotent U → SubgroupFunctor.range (𝟙 U) ≠ ⊥ →
      ∃ z : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ U,
        IsClosedSubgroup z ∧ IsCentral z

end Langlands.GroupScheme
