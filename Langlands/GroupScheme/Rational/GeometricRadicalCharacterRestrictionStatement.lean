import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Rational.LeviSubgroup

/-! # Rational and geometric characters of a reductive group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Rational characters embed in geometric characters by base change.
Restriction of geometric characters to the geometric solvable radical is
injective with finite-index image. -/
def GeometricRadicalCharacterRestrictionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G R : GroupScheme (Spec (CommRingCat.of k))) (r : R ⟶ G),
    IsConnectedReductive G → IsGeometricSolvableRadical r →
      let b := toAlgebraicClosure k
      let rbar := (GroupScheme.baseChange b).map r
      Function.Injective (rationalCharacters.baseChange b (G := G)) ∧
        Function.Injective (characterRestrict rbar) ∧
        (characterRestrict rbar).range.FiniteIndex

end Langlands.GroupScheme
