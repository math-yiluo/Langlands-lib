import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Langlands.GroupScheme.Dynamic.Basic

/-! # Statement: smooth connected fibres of dynamic subgroups over a ring -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Dynamic subgroups of a smooth affine group over a ring** (Conrad, *Reductive group
schemes* (2014), Theorem 4.1.7(2) and the smoothness assertion of 4.1.7(4), for the conjugation
action of a cocharacter). Let `G` be a smooth affine group scheme over `Spec R`, `R` any
commutative ring, and `χ` a cocharacter of `G`. Every representative of `U_G(χ)` is smooth with
geometrically connected fibres. Every representative of `P_G(χ)` or `Z_G(χ)` is smooth, and
has geometrically connected fibres when `G` does. -/
def DynamicRingSmoothConnectedStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (G : GroupScheme (Spec (CommRingCat.of R)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G)
    (H : GroupScheme (Spec (CommRingCat.of R))) (j : H ⟶ G),
    ((Dynamic.unipotent χ).IsRepresentedBy j →
      Smooth H.X.hom ∧ GeometricallyConnected H.X.hom) ∧
    ((Dynamic.parabolic χ).IsRepresentedBy j →
      Smooth H.X.hom ∧ (GeometricallyConnected G.X.hom → GeometricallyConnected H.X.hom)) ∧
    ((Dynamic.centralizer χ).IsRepresentedBy j →
      Smooth H.X.hom ∧ (GeometricallyConnected G.X.hom → GeometricallyConnected H.X.hom))

end Langlands.GroupScheme
