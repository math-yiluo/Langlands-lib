import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.RelativeIdentityComponent
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Affineness from connected reductive residue fibres -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth separated finitely presented group scheme whose residue-field
fibres are all connected reductive is affine over the base.

This is the everywhere-reductive consequence of SGA 3, Exposé XVI,
Theorem 5.2(i): its reductive open neighbourhoods cover the base. -/
def ReductiveFiberAffinenessStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
    (∀ s : S, IsConnectedReductive (RelativeIdentityComponent.residueFiber G s)) →
      IsAffineHom G.X.hom

end Langlands.GroupScheme
