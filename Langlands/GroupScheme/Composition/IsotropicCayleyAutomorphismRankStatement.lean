import Langlands.GroupScheme.Composition.CayleyDatum
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Split rank of an actual automorphism group of an isotropic Cayley algebra -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field, an actual group scheme realizing the full algebra
automorphism functor of a Cayley datum with isotropic norm has split rank two.
This general structural statement is unproved. -/
def IsotropicCayleyAutomorphismRankStatement : Prop :=
  ∀ (K : Type u) [Field K] (c : CayleyDatum K)
    (H : GroupScheme (Spec (CommRingCat.of K)))
    (iH : H ⟶ GeneralLinear.groupScheme (Fin 8) (CommRingCat.of K)),
    c.IsAutomorphismRepresentation iH →
    (∃ x : CayleyVector K, x ≠ 0 ∧ c.norm x = 0) →
      splitRank H = 2

end Langlands.GroupScheme
