import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Unipotence of dynamic unipotent subgroups over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every representative of the dynamic subgroup `U_G(χ)` of an affine group of
finite type over a field is unipotent in the representation-theoretic sense.
No proof is supplied. -/
def DynamicUnipotentUnipotenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
    (Dynamic.unipotent χ).IsRepresentedBy j → IsUnipotent H

end Langlands.GroupScheme
