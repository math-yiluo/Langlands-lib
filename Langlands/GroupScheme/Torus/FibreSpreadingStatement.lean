import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.RelativeIdentityComponent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Statement: a torus fibre spreads to a Zariski neighbourhood -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **A torus fibre spreads out** (Conrad, *Reductive group schemes* (2014), Corollary 3.1.8;
SGA 3, X, 4.9). Let `G → S` be an fppf `S`-affine group scheme whose fibres over the residue
fields are connected, and suppose the fibre `G_s` at some point `s ∈ S` is a torus over
`k(s)`. Then there is an open neighbourhood `U` of `s` such that `G_U` is a torus over `U`
(an étale form of split tori). -/
def TorusFibreSpreadingStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]
    [IsAffineHom G.X.hom],
    (∀ s : S, ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left) →
    ∀ s : S, IsTorus (RelativeIdentityComponent.residueFiber G s) →
      ∃ U : S.Opens, s ∈ U ∧ RelativeTorus.IsTorus ((GroupScheme.baseChange U.ι).obj G)

end Langlands.GroupScheme
