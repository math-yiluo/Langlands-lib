import Langlands.GroupScheme.Rational.RootFactorizationFromExistence
import Langlands.GroupScheme.Rational.RootRankOneFactorizationStatement

/-! # Opposite factor pairs over algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Opposite factor pairs over algebraically closed fields** (existence part of
Kaletha–Prasad 2.11.17 and Conrad–Gabber–Prasad C.2.24(i), specialized to connected
reductive groups over algebraically closed fields). For every actual maximal split torus
`i`, every nonidentity rational point `u` of the actual root group of a relative root `a`
has rational points `u′, u′′` of the root group of `-a` with `u′ * u * u′′` normalizing
the torus. -/
def AlgClosedOppositeFactorPairsStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    RelativeRoot.HasOppositeFactorPairs i

end Langlands.GroupScheme
