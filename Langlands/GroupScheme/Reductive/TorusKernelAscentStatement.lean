import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement

/-! # Reductivity ascent for affine groups with torus kernel -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An affine source of an actual fppf quotient with a full closed torus kernel
is connected reductive if its quotient is connected reductive. -/
def TorusKernelReductiveAscentStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (E G T : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom E.X.hom]
    (i : T ⟶ E),
    IsClosedSubgroup i → IsTorus T →
    ∀ (p : E ⟶ G),
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) p →
      IsConnectedReductive G → IsConnectedReductive E

end Langlands.GroupScheme
