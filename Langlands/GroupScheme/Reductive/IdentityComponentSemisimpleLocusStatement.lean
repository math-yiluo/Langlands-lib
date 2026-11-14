import Langlands.GroupScheme.Reductive.IdentityComponentLocus
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Statement: the semisimple identity-component locus is open -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Openness of the semisimple identity-component locus** (Conrad, *Reductive group
schemes* (2014), Proposition 3.1.9(1), semisimple case). For a smooth `S`-affine group
scheme `G`, the set of points `s ∈ S` at which the identity component of the geometric
fibre `G_{s̄}` is semisimple is open in `S`. -/
def IdentityComponentSemisimpleLocusOpenStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    IsOpen {s : S |
      haveI : Smooth (geometricFiber G s).X.hom :=
        inferInstanceAs (Smooth (Limits.pullback.snd G.X.hom (geometricPoint S s)))
      haveI : IsAffineHom (geometricFiber G s).X.hom :=
        inferInstanceAs (IsAffineHom (Limits.pullback.snd G.X.hom (geometricPoint S s)))
      IsSemisimple (identityComponent (geometricFiber G s))}

end Langlands.GroupScheme
