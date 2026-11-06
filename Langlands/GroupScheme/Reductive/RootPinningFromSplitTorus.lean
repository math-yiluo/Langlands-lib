import Langlands.GroupScheme.Reductive.PinningExistenceStatement
import Langlands.GroupScheme.Reductive.PinningConstruction
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof

/-! # Root pinnings for split maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Choose simple-root trivializations for the supplied actual split maximal
torus, realized root datum and base, using the proved root-line theorem. -/
def RootPinning.ofSplitMaximalTorus
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G) {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i)
    {J : Type u} (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (hP : letI := hG.isAffineHom; IsRootDatumOf i P) (b : P.Base) :
    letI := hG.isAffineHom
    RootPinning i P b := by
  let := hG.isAffineHom
  exact RootPinning.ofRootLines i P hP b
    (splitRootLieLine k G hG T hT i hi)

/-- Every base of a realized root datum of a split maximal torus admits
simple-root Lie trivializations over the original field. -/
theorem rootPinningExistence : RootPinningExistenceStatement.{u} := by
  intro k _ G hG T hT i hi
  let := hG.isAffineHom
  intro J P hP b
  exact ⟨RootPinning.ofSplitMaximalTorus hG hT i hi P hP b⟩

/-- The proved root-line theorem leaves only root-datum existence as a
structural premise for constructing a split pinning. -/
theorem splitPinningExistence_of_rootDatumExistence
    (hroot : RootDatumExistenceStatement.{u}) :
    SplitPinningExistenceStatement.{u} := by
  intro k _ G hG T hT i hi
  let := hG.isAffineHom
  exact ⟨SplitPinning.ofRootDatumExistence hroot hG hT i hi
    (splitRootLieLine k G hG T hT i hi)⟩

end Langlands.GroupScheme
