import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Reductive.Basic

/-! # Finite-index restriction of rational characters to a split component

The finite-index conclusion of `CharacterRestrictionStatement`, stated separately without proof.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field `k`, for a split component `i : A ⟶ G` of a connected reductive group `G`,
the range of the restriction `X^*(G)_k → X^*(A)` has finite index in `X^*(A)`. -/
def CharacterRestrictionFiniteIndexStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ (A : CommGroupScheme (Spec (CommRingCat.of k))) (i : A.toGrp ⟶ G), IsSplitComponent i →
      (characterRestrict i).range.FiniteIndex

end Langlands.GroupScheme
