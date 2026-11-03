import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Rational.SubgroupConjugacy

/-! # Rational conjugacy of maximal tori in smooth connected solvable groups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over every field, any two maximal tori of a smooth connected affine solvable
group scheme are conjugate by a rational point, with an isomorphism of their sources. -/
def SolvableMaximalTorusConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsSolvableGroupScheme G →
    ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (i' : T'.toGrp ⟶ G), IsMaximalTorus i → IsMaximalTorus i' →
        SubgroupConjugate i i'

end Langlands.GroupScheme
