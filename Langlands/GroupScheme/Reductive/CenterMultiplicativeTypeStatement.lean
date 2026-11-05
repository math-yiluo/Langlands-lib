import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Torus.MultiplicativeType

/-! # The full center of a connected reductive group is of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Chapter 19, printed p.400: every actual representative of the full
scheme-theoretic center of a connected reductive group over a field is of
multiplicative type, including its nonsmooth and disconnected factors. -/
def CenterMultiplicativeTypeStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G Z : GroupScheme (Spec (CommRingCat.of k))) (z : Z ⟶ G),
    IsConnectedReductive G → IsSchemeTheoreticCenter z → IsMultiplicativeType Z

end Langlands.GroupScheme
