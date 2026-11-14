import Langlands.GroupScheme.Reductive.IdentityComponentLocus
import Langlands.GroupScheme.RelativeIdentityComponent

/-! # Statement: the locus of connected fibres is closed -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The connected-fibre locus is closed** (Conrad, *Reductive group schemes* (2014),
Proposition 3.1.12). Let `G → S` be a smooth `S`-affine group scheme such that the identity
component of every geometric fibre is reductive. Then the set of points `s ∈ S` whose fibre
`G_s` over the residue field `k(s)` is connected is closed in `S`. In particular, if `η` is a
generic point of `S` (so `S` is irreducible) and the generic fibre `G_η` is connected, then
every fibre `G_s` is connected. -/
def ConnectedFibreLocusClosedStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    identityComponentReductiveLocus G = Set.univ →
      let ConnectedFibre : S → Prop := fun s =>
        ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left
      IsClosed {s : S | ConnectedFibre s} ∧
        ∀ η : S, IsGenericPoint η Set.univ → ConnectedFibre η → ∀ s : S, ConnectedFibre s

end Langlands.GroupScheme
