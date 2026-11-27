import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.SubgroupIntersection

/-! # The cocenter as a quotient of the solvable radical -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The actual quotient by the derived subgroup is also the quotient of the
geometric solvable radical by its intersection with the derived subgroup.
Pullback along the cocenter quotient identifies the actual character groups. -/
def ReductiveCocenterRadicalQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G R D : GroupScheme (Spec (CommRingCat.of k)))
    (r : R ⟶ G) (d : D ⟶ G),
    IsConnectedReductive G → IsGeometricSolvableRadical r → IsDerivedSubgroup d →
      ∀ (Q : CommGroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q.toGrp),
        IsTorus Q.toGrp → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range d) q →
          RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (subgroupIntersectionFst r d))
            (r ≫ q) ∧ Function.Bijective (characterRestrict q)

end Langlands.GroupScheme
