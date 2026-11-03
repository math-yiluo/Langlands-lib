import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Statement: a central extension of a torus by a torus is a torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A central extension of a torus by a torus over a field is a torus (Milne 12.41 and 12.22):
if `z : Z ⟶ E` is a central closed subgroup with `Z` a torus and `p : E ⟶ T` is an affine fppf
quotient map onto a torus `T` with kernel `Z`, then `E` is a torus. -/
def CentralTorusExtensionStatement : Prop :=
  ∀ (k : Type u) [Field k] (E : GroupScheme (Spec (CommRingCat.of k)))
    (Z : CommGroupScheme (Spec (CommRingCat.of k))) (z : Z.toGrp ⟶ E),
    IsTorus Z.toGrp → IsClosedSubgroup z → IsCentral z →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (p : E ⟶ T.toGrp), IsTorus T.toGrp →
      IsAffineHom p.hom.hom.left → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) p →
        IsTorus E

end Langlands.GroupScheme
