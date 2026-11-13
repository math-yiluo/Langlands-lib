import Langlands.GroupScheme.Quaternionic.SpinKernelAdaptedReduction
import Langlands.GroupScheme.Quaternionic.SpinKernelSplitCoordinates
import Langlands.GroupScheme.Quaternionic.DegreeTwoNormOneSimplyConnectedProof

/-! # Assembly of the quaternionic spin-kernel generator statement -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

/-- The original Levi lifts identify `μ₂` with the kernel of every quaternionic spin
cover in the stated local-field setting, on all coefficient algebras. -/
theorem spinKernelGenerator : SpinKernelGeneratorStatement.{u} := by
  intro K _ _ _ _ D _ _ _ _ hdim σ hsym m hm q hq _ S π hπ v w h mu psi hlift
  let : Infinite K := Langlands.LocalField.infinite_of_isNonarchimedeanLocalField K
  obtain ⟨k, _, ⟨e⟩⟩ := Langlands.CentralSimple.exists_matrix_chart K D (AlgebraicClosure K)
  have hk : k = 2 := by
    have hd := Langlands.CentralSimple.finrank_eq_matrix_size K D (AlgebraicClosure K) k e
    rw [hdim] at hd
    exact Nat.mul_self_inj.mp (hd.symm.trans rfl)
  subst hk
  have hm0 : 0 < m := by omega
  obtain ⟨Φ, hΦ⟩ := SplitCoordinates.exists_adaptedCoordinates e σ hsym hm0 hq h
  exact kernelGenerator_of_adaptedCoordinates e σ h Φ ⟨0, hm0⟩ hdim hsym hπ
    CentralSimpleUnits.degreeTwoNormOneSimplyConnected hΦ
    (by rw [Fintype.card_fin]; omega) hlift

end Langlands.GroupScheme.Quaternionic.SpinKernel
