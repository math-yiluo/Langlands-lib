import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: the image of a torus in an affine group of finite presentation -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Image of a torus in an affine group** (SGA 3, Exposé IX, Théorème 6.8
with its N.B. and Remarque 6.6.1, together with Exposé X, Corollaire 4.5).

Let `S` be a scheme, `T` a commutative group scheme over `S` which is a torus,
and `u : T.toGrp ⟶ G` a homomorphism into a group scheme `G` which is affine and
locally of finite presentation over `S`. Then `u = π ≫ ι` where `D` is a torus
over `S`, `ι : D.toGrp ⟶ G` is a closed subgroup inclusion and the underlying
morphism of `π : T.toGrp ⟶ D.toGrp` is flat, surjective and locally of finite
presentation. -/
def RelativeTorusImageFactorizationStatement : Prop :=
  ∀ (S : Scheme.{u}) (T : CommGroupScheme S) (G : GroupScheme S) (u : T.toGrp ⟶ G),
    RelativeTorus.IsTorus T.toGrp → IsAffineHom G.X.hom →
    LocallyOfFinitePresentation G.X.hom →
    ∃ (D : CommGroupScheme S) (π : T.toGrp ⟶ D.toGrp) (ι : D.toGrp ⟶ G),
      RelativeTorus.IsTorus D.toGrp ∧ IsClosedSubgroup ι ∧
        Flat π.hom.hom.left ∧ Surjective π.hom.hom.left ∧
        LocallyOfFinitePresentation π.hom.hom.left ∧ π ≫ ι = u

end Langlands.GroupScheme
