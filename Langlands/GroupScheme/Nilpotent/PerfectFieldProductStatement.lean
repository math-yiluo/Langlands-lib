import Langlands.GroupScheme.Nilpotent.Basic
import Mathlib.FieldTheory.Perfect

/-! # Statement: connected nilpotent group varieties over a perfect field -/

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

namespace Langlands.GroupScheme

/-- **Connected nilpotent group varieties over a perfect field** (Milne, *Algebraic Groups*
(2017), Corollary 16.48). Over a perfect field `k`, a smooth connected affine group scheme `G`
is nilpotent if and only if it is isomorphic, as a group scheme, to a product `U × T` of a
smooth connected affine unipotent group scheme `U` and a torus `T`. -/
def NilpotentPerfectFieldProductStatement : Prop :=
  ∀ (k : Type u) [Field k] [PerfectField k] (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom → ConnectedSpace G.X.left →
      (IsNilpotentGroupScheme G ↔
        ∃ (U T : GroupScheme (Spec (CommRingCat.of k))),
          Smooth U.X.hom ∧ IsAffineHom U.X.hom ∧ ConnectedSpace U.X.left ∧ IsUnipotent U ∧
            IsTorus T ∧ Nonempty (G ≅ U ⊗ T))

end Langlands.GroupScheme
