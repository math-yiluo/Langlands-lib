import Langlands.AlgebraicGeometry.Picard.PositiveTensorPowerAmpleStatement
import Langlands.AlgebraicGeometry.Picard.AmpleIsoProof
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Langlands.AlgebraicGeometry.Modules.PositiveSectionPowerGenerationLocusProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms

/-! # Ampleness under positive tensor powers and sheaf isomorphisms -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

open Langlands.SchemeModule Langlands.Scheme.Modules

/-- Any actual line bundle isomorphic to a positive tensor power of an ample
line bundle is ample. -/
theorem positiveTensorPowerAmple : PositiveTensorPowerAmpleStatement.{u} := by
  intro X L M n hn hL he
  obtain ⟨e⟩ := he
  refine ⟨hL.1, fun x ↦ ?_⟩
  obtain ⟨k, hk, s, hx, ha⟩ := hL.2 x
  let K : LineBundle X :=
    ⟨tensorPow L.obj k, tensorPow_isLocallyFreeRankOne X L k⟩
  let a : tensorPow K.obj n ≅ tensorPow M.obj k :=
    tensorPowMulIso L.obj k n ≪≫
      eqToIso (congrArg (tensorPow L.obj) (Nat.mul_comm k n)) ≪≫
      (tensorPowMulIso L.obj n k).symm ≪≫ (tensorPowIso e k).symm
  let t : M.powSections k := a.hom.app ⊤ (sectionPow K.obj s n)
  have h : M.sectionOpen t = L.sectionOpen s := by
    change trivializationOpen (tensorPow M.obj k)
      (a.hom.app ⊤ (sectionPow K.obj s n)) = trivializationOpen K.obj s
    rw [trivializationOpen_mapIso, trivializationOpen_sectionPow K s hn]
  exact ⟨k, hk, t, h ▸ hx, h ▸ ha⟩

end Langlands.AlgebraicGeometry.Picard
