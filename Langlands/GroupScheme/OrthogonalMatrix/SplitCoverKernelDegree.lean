import Langlands.GroupScheme.OrthogonalMatrix.CentralCoverKernel
import Langlands.GroupScheme.HomScheme.FiniteDiagonalizableHom
import Langlands.GroupScheme.AffinePoints
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # The kernel degree of a split even orthogonal cover -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrthogonalMatrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {l : Type} [Fintype l] [DecidableEq l] {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {p : G ⟶ identityComponent (groupScheme l (CommRingCat.of k))}
  (hp : IsCentralIsogeny p) (hG : IsSimplyConnected G) (hl : 3 ≤ Fintype.card l)

local notation "Rbase" => CommRingCat.of k
local notation "S" => Spec Rbase
local notation "D" => splitTorus.commGroupScheme S (ULift l)

include hp hG hl

/-- The full kernel of a simply connected cover of the split even orthogonal identity
component is the one-factor product of square roots of unity. -/
def splitCoverKernelIso : kernel p ≅ HomScheme.FiniteDiagonalizable.muPower k PUnit.{u+1} 2 := by
  apply Classical.choice
  let : Nontrivial l := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have hD : IsSplitTorus (D).toGrp := SymplecticMatrix.isSplitTorus_diagonalTorus l k
  obtain ⟨T, i, t, hT, hi, ht⟩ := centralIsogenySplitMaximalTorusLift k G _
    hG.isSemisimple.isConnectedReductive (isConnectedReductive_identityComponent l k)
    p hp D (identityTorus l k) hD (isMaximalTorus_identityTorus l k)
  let e := hp.indexTwoKernelIso hG.isSemisimple.isConnectedReductive hT hD hi
    (isClosedSubgroup_identityTorus l k) t ht (card_centralCoverQuotient hp hG hT hi t ht hl)
  let a : ULift.{u} (ZMod 2) ≃+ (PUnit.{u+1} → ZMod 2) :=
    AddEquiv.ulift.trans (AddEquiv.piUnique (fun _ : PUnit.{u+1} => ZMod 2)).symm
  exact ⟨e.symm ≪≫ Diagonalizable.congrIso Rbase a ≪≫ HomScheme.FiniteDiagonalizable.diagonalizableIso k _ 2⟩

variable [CharZero k]

/-- Over a characteristic-zero splitting field, the geometric kernel of the simply
connected vector cover of the even orthogonal group has exactly two points. -/
theorem natCard_splitCoverKernel_points :
    Nat.card (affinePoints (kernel p) (CommAlgCat.of k k)) = 2 := by
  let A := CommAlgCat.of k k
  let T := (algSpec Rbase).obj (op A)
  let e := (((yonedaGrp.mapIso (splitCoverKernelIso hp hG hl)).app (op T)).groupIsoToMulEquiv).toEquiv
  let v := piPointsEquiv (fun _ : PUnit.{u+1} => (mu S 2).toGrp) T
  let a := Equiv.piUnique (fun _ : PUnit.{u+1} => affinePoints (mu S 2).toGrp A)
  let b := (mu.affinePointsEquiv 2 (Spec.algebraMap k k)).toEquiv
  exact (Nat.card_congr (e.trans (v.toEquiv.trans (a.trans b)))).trans
    ((IsPrimitiveRoot.neg_one (R := k) 0 (by decide)).card_rootsOfUnity)

end Langlands.GroupScheme.OrthogonalMatrix
