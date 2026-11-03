import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Lattice

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over every field `k`, every nonzero rational character `χ ∈ X^*(G)_k` of a connected reductive
group `G` restricts to a nonzero character of some central closed subtorus `i : Z ⟶ G`, where `Z`
is affine and locally of finite type over `k`. -/
def CentralTorusCharacterStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))), IsConnectedReductive G →
    ∀ χ : rationalCharacters G, χ ≠ 0 →
      ∃ (Z : CommGroupScheme (Spec (CommRingCat.of k))) (i : Z.toGrp ⟶ G),
        IsAffineHom Z.toGrp.X.hom ∧ LocallyOfFiniteType Z.toGrp.X.hom ∧ IsTorus Z.toGrp ∧
          IsClosedSubgroup i ∧ IsCentral i ∧ characterRestrict i χ ≠ 0

end Langlands.GroupScheme
