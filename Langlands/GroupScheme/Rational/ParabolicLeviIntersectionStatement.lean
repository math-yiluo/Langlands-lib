import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.SplitTorus

/-! # Intersection of a Levi subgroup with a parabolic sharing a maximal split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Let `p : P ⟶ G` and `q : Q ⟶ G` be actual parabolic subgroups of a connected reductive
group over a field, with rational Levi subgroups `l : M ⟶ P` and `lQ : L ⟶ Q`, and let
`rQ : U ⟶ Q` be the geometric unipotent radical of `Q` complementary to `L`. If `M` and `L`
contain a common maximal split torus of `G`, then `M ∩ Q` is represented by an actual
parabolic subgroup `p' : P' ⟶ M` of `M`, with a rational Levi `l' : M' ⟶ P'` representing
`M ∩ L` and a complementary geometric unipotent radical `r' : N' ⟶ P'` representing `M ∩ U`.
The intersections are infima of all-test subgroup functors of `G`. -/
def RepresentedParabolicLeviIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : IsConnectedReductive G)
    (P M Q L U : GroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ G) (l : M ⟶ P) (_hp : IsParabolicSubgroup p) (_hl : IsRationalLeviSubgroup l)
    (q : Q ⟶ G) (lQ : L ⟶ Q) (rQ : U ⟶ Q) (_hq : IsParabolicSubgroup q)
    (_hlQ : IsRationalLeviSubgroup lQ) (_hrQ : LeviSubgroup.IsGeometricUnipotentRadical rQ)
    (_hmulQ : IsIso (subgroupMultiplication lQ rQ))
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
    IsMaximalSplitTorus i → (∃ a : T.toGrp ⟶ M, a ≫ l ≫ p = i) →
      (∃ b : T.toGrp ⟶ L, b ≫ lQ ≫ q = i) →
      ∃ (P' M' N' : GroupScheme (Spec (CommRingCat.of k)))
        (p' : P' ⟶ M) (l' : M' ⟶ P') (r' : N' ⟶ P'),
        IsParabolicSubgroup p' ∧ LeviSubgroup.IsGeometricUnipotentRadical r' ∧
          IsRationalLeviSubgroup l' ∧ IsIso (subgroupMultiplication l' r') ∧
          SubgroupFunctor.range (p' ≫ l ≫ p) =
            SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range q ∧
          SubgroupFunctor.range (l' ≫ p' ≫ l ≫ p) =
            SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (lQ ≫ q) ∧
          SubgroupFunctor.range (r' ≫ p' ≫ l ≫ p) =
            SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range (rQ ≫ q)

end Langlands.GroupScheme
