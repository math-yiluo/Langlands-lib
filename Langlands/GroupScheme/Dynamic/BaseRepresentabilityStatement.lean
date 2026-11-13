import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Langlands.GroupScheme.Dynamic.Basic

/-! # Statement: representability of dynamic subgroups over any base scheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Dynamic subgroups over any base scheme are finitely presented closed subgroups**
(Conrad, *Reductive group schemes* (2014), Theorem 4.1.7(1), representability part, for the
conjugation action of a cocharacter, over a base scheme `S` that need not be affine). Let `G`
be a group scheme over `S` whose structure morphism is affine and locally of finite
presentation, and `χ` a cocharacter of `G`. Each of the subgroup functors `P_G(χ)`, `U_G(χ)`
and `Z_G(χ)` is represented by a homomorphism `j : H ⟶ G` whose underlying morphism of schemes
is a closed immersion, with `H` locally of finite presentation over `S`. -/
def DynamicBaseRepresentabilityStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [IsAffineHom G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] (χ : (Gm S).toGrp ⟶ G),
    (∃ (H : GroupScheme S) (j : H ⟶ G), IsClosedImmersion j.hom.hom.left ∧
      LocallyOfFinitePresentation H.X.hom ∧ (Dynamic.parabolic χ).IsRepresentedBy j) ∧
    (∃ (H : GroupScheme S) (j : H ⟶ G), IsClosedImmersion j.hom.hom.left ∧
      LocallyOfFinitePresentation H.X.hom ∧ (Dynamic.unipotent χ).IsRepresentedBy j) ∧
    (∃ (H : GroupScheme S) (j : H ⟶ G), IsClosedImmersion j.hom.hom.left ∧
      LocallyOfFinitePresentation H.X.hom ∧ (Dynamic.centralizer χ).IsRepresentedBy j)

end Langlands.GroupScheme
