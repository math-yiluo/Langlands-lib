import Langlands.Global.Arithmetic.AlmostEverywherePowerHalfStatement
import Langlands.Global.Arithmetic.IdeleClassPowerQuotientProfiniteProof
import Langlands.Global.Arithmetic.PrescriptionLocalPowerIndex
import Langlands.Global.Arithmetic.PrescriptionPowerIntersectionReduction
import Langlands.Global.Arithmetic.CharacterPrescriptionAssembly
import Langlands.Topology.ProfiniteFiniteImageSeparation

/-! # The two arithmetic inputs to finite-order character prescription -/

noncomputable section

universe u

namespace Langlands.Global

set_option maxHeartbeats 800000 in
/-- Almost-everywhere half-power descent and profiniteness of the actual
idele-class power quotients imply the finite-quotient prescription assertion. -/
theorem prescriptionFiniteQuotient_of_halfPower_and_profinite
    (hhalf : AlmostEverywherePowerHalfStatement.{u})
    (hprofinite : IdeleClassPowerQuotientProfiniteStatement.{u}) :
    PrescriptionFiniteQuotientStatement.{u} := by
  intro K _ _ S n hn U _ hU
  have hQ := hprofinite K (2 * n) (by omega)
  let : T2Space (IdeleClasses K ⧸
      (powMonoidHom (α := IdeleClasses K) (2 * n)).range) := hQ.1
  let : CompactSpace (IdeleClasses K ⧸
      (powMonoidHom (α := IdeleClasses K) (2 * n)).range) := hQ.2.1
  let : TotallyDisconnectedSpace (IdeleClasses K ⧸
      (powMonoidHom (α := IdeleClasses K) (2 * n)).range) := hQ.2.2
  let : (powMonoidHom (α := PrescriptionLocalProduct K S) (2 * n)).range.FiniteIndex :=
    prescriptionLocalProduct_power_finiteIndex K S (2 * n) (by omega)
  obtain ⟨N, hNopen, hNfinite, hNpower, hNpre⟩ :=
    Langlands.Topology.exists_open_subgroup_from_power_intersection
      (A := PrescriptionLocalProduct K S) (C := IdeleClasses K)
      (prescriptionClassMap K S) (2 * n) n U.toSubgroup hU
      (prescription_power_preimage_le_of_half_power K S n (hhalf K S n hn))
  exact ⟨⟨N, hNopen⟩, hNfinite, hNpower, hNpre⟩

/-- The two precise arithmetic prerequisites suffice for the unchanged
finite-order prescription target, with its whole infinity component and
unconditional doubled exponent in the conclusion. -/
theorem finiteOrderCharacterPrescription_of_halfPower_and_profinite
    (hhalf : AlmostEverywherePowerHalfStatement.{u})
    (hprofinite : IdeleClassPowerQuotientProfiniteStatement.{u}) :
    FiniteOrderCharacterPrescriptionStatement.{u} :=
  finiteOrderCharacterPrescription_of_finiteQuotient
    (prescriptionFiniteQuotient_of_halfPower_and_profinite hhalf hprofinite)

/-- Almost-everywhere half-power descent suffices for the finite-quotient
prescription assertion, using the proved topology of idele-class power quotients. -/
theorem prescriptionFiniteQuotient_of_halfPower
    (hhalf : AlmostEverywherePowerHalfStatement.{u}) :
    PrescriptionFiniteQuotientStatement.{u} :=
  prescriptionFiniteQuotient_of_halfPower_and_profinite
    hhalf ideleClassPowerQuotientProfinite_proof

/-- Almost-everywhere half-power descent suffices for finite-order character
prescription, using the proved topology of idele-class power quotients. -/
theorem finiteOrderCharacterPrescription_of_halfPower
    (hhalf : AlmostEverywherePowerHalfStatement.{u}) :
    FiniteOrderCharacterPrescriptionStatement.{u} :=
  finiteOrderCharacterPrescription_of_finiteQuotient
    (prescriptionFiniteQuotient_of_halfPower hhalf)

end Langlands.Global
