import Langlands.GroupScheme.Rational.MaximalSplitTorusStatement
import Langlands.GroupScheme.Absolute.Borel

/-! # Conjugacy of maximal split tori in smooth connected solvable groups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over every field, the maximal split tori of a smooth connected affine
solvable group scheme are conjugate by a rational point. -/
def SolvableMaximalSplitTorusConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsSolvableGroupScheme G →
    ∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (i' : T'.toGrp ⟶ G), IsMaximalSplitTorus i → IsMaximalSplitTorus i' →
        ∃ (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
          (e : T.toGrp ≅ T'.toGrp),
          i ≫ (G.innerIso g).hom = e.hom ≫ i'

end Langlands.GroupScheme
