import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Dynamic.Basic

/-! # Statement: over a finite field, a group whose cocharacters are all central is solvable -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Over a finite field, if every cocharacter of a smooth connected affine group is central
(its dynamic centralizer is the whole group on every test scheme), then the group is
solvable. -/
def FiniteFieldCentralCocharacterSolvableStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G, Dynamic.centralizer χ = ⊤) →
      IsSolvableGroupScheme G

end Langlands.GroupScheme
