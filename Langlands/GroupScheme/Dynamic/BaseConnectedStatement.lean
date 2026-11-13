import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Langlands.GroupScheme.Dynamic.Basic

/-! # Statement: connected fibres of dynamic subgroups without smoothness -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Connected fibres of dynamic subgroups over any base scheme** (Conrad, *Reductive
group schemes* (2014), Theorem 4.1.7(2) and the arbitrary-base paragraph after Example 4.1.9).
For an affine locally finitely presented group scheme `G` over any scheme `S` and a
cocharacter `χ`, every representative of `U_G(χ)` has geometrically connected fibres.
Every representative of `P_G(χ)` or `Z_G(χ)` has geometrically connected fibres if `G`
does. No smoothness hypothesis is made. -/
def DynamicBaseConnectedStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] (χ : (Gm S).toGrp ⟶ G)
    (H : GroupScheme S) (j : H ⟶ G),
    ((Dynamic.unipotent χ).IsRepresentedBy j → GeometricallyConnected H.X.hom) ∧
    ((Dynamic.parabolic χ).IsRepresentedBy j →
      GeometricallyConnected G.X.hom → GeometricallyConnected H.X.hom) ∧
    ((Dynamic.centralizer χ).IsRepresentedBy j →
      GeometricallyConnected G.X.hom → GeometricallyConnected H.X.hom)

end Langlands.GroupScheme
