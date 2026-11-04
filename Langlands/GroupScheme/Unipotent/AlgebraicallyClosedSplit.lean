import Langlands.GroupScheme.Unipotent.AlgebraicallyClosedSplitReduction
import Langlands.GroupScheme.Unipotent.OneDimensional.Proof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof

/-! # Represented split series for unipotent groups over algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Unipotent

/-- Every smooth connected affine unipotent group over an algebraically closed
field has a finite represented series with one-dimensional vector quotients. -/
theorem algebraicallyClosedSplit
    (k : Type u) [Field k] [IsAlgClosed k]
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom]
    (hUc : ConnectedSpace U.X.left) (hUu : IsUnipotent U) :
    RelativeRoot.IsSplitUnipotent U :=
  algebraicallyClosedSplit_of_oneDimensional
    unipotentClosedSubgroup perfectFieldOneDimensionalUnipotent k U hUc hUu

/-- A chosen length and the full represented split-series witness, with no
additional structural inputs. -/
def algebraicallyClosedSeries
    (k : Type u) [Field k] [IsAlgClosed k]
    (U : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth U.X.hom] [IsAffineHom U.X.hom]
    (hUc : ConnectedSpace U.X.left) (hUu : IsUnipotent U) :
    {n : ℕ // RelativeRoot.HasSplitSeries n U} :=
  algebraicallyClosedSplitSeries
    unipotentClosedSubgroup perfectFieldOneDimensionalUnipotent k U hUc hUu

end Langlands.GroupScheme.Unipotent
