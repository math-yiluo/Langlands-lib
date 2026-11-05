import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Cartier smoothness in characteristic zero -/

universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every affine group scheme locally of finite type over a characteristic-zero
field is smooth over that field. No reducedness or smoothness premise is made. -/
def AffineCartierSmoothStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
      IsAffineHom G.X.hom → LocallyOfFiniteType G.X.hom → Smooth G.X.hom

end Langlands.GroupScheme
