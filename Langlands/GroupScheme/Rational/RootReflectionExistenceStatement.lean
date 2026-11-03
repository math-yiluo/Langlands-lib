import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.GroupScheme.Rational.RootSubgroup

/-! # Intrinsic existence of integral relative-root reflections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual relative root of a maximal split torus in a connected
reductive group has integral reflection data represented by a rational point
centralizing the full scheme-theoretic kernel of that root. -/
def RelativeRootReflectionExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∃ D : RelativeRootReflectionData i, ∀ a : relativeRoots i,
      (D.representative a).val ∈
        (RelativeRoot.kernelCentralizer i a.val).carrier (Over.mk (𝟙 _))

end Langlands.GroupScheme
