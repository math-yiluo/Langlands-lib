import Langlands.AbelianScheme.Basic

/-! # Equivalence with the source definition of an abelian scheme -/

universe u

open AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Every smooth proper group scheme with geometrically connected fibres admits
the explicit-commutativity bundle, with exactly the same underlying group scheme. -/
def SourceDefinitionEquivalence : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S),
    GroupScheme.IsAbelian G ↔ ∃ A : AbelianScheme S, A.toGrp = G

end Langlands.AbelianScheme
