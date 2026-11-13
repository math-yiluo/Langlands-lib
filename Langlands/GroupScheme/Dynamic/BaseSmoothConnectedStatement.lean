import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Langlands.GroupScheme.Dynamic.Basic

/-! # Statement: smooth connected fibres of dynamic subgroups over any base scheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Dynamic subgroups of a smooth affine group over any base scheme** (Conrad, *Reductive group
schemes* (2014), Theorem 4.1.7(2) and the smoothness assertion of 4.1.7(4), for the conjugation
action of a cocharacter, over a base scheme `S` that need not be affine). Let `G` be a group
scheme over `S` whose structure morphism is smooth and affine, and `χ` a cocharacter of `G`.
Every representative of `U_G(χ)` is smooth over `S` with geometrically connected fibres. Every
representative of `P_G(χ)` or `Z_G(χ)` is smooth over `S`, and has geometrically connected
fibres when `G` does. -/
def DynamicBaseSmoothConnectedStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) (H : GroupScheme S) (j : H ⟶ G),
    ((Dynamic.unipotent χ).IsRepresentedBy j →
      Smooth H.X.hom ∧ GeometricallyConnected H.X.hom) ∧
    ((Dynamic.parabolic χ).IsRepresentedBy j →
      Smooth H.X.hom ∧ (GeometricallyConnected G.X.hom → GeometricallyConnected H.X.hom)) ∧
    ((Dynamic.centralizer χ).IsRepresentedBy j →
      Smooth H.X.hom ∧ (GeometricallyConnected G.X.hom → GeometricallyConnected H.X.hom))

end Langlands.GroupScheme
