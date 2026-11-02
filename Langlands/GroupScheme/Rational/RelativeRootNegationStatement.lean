import Langlands.GroupScheme.Rational.RelativeRoots

/-! # Negation stability of the actual relative roots -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The actual relative roots of a maximal split torus in a connected
reductive group over any field are stable under negation, with no
root-system premise. -/
def RelativeRootNegationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (_hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i

end Langlands.GroupScheme
