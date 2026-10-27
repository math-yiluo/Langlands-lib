import Langlands.Representation.Parabolic.ThreeBlockCarrierComparison
import Langlands.Representation.Parabolic.ThreeBlockInductionAssociativityStatement

/-! Reduction of literal heterogeneous associativity to a common carrier universe. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Parabolic

open Shahidi

universe uF uW uV0 uV1 uV2

/-- Associativity for three smooth factors in a common carrier universe. -/
def CommonUniverseThreeBlockAssociativity : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (C A B : ℕ) (hC : 0 < C) (hA : 0 < A) (hB : 0 < B)
    {W0 W1 W2 : Type (max uF uW)}
    [AddCommGroup W0] [Module ℂ W0]
    [AddCommGroup W1] [Module ℂ W1]
    [AddCommGroup W2] [Module ℂ W2]
    (τ0 : Representation ℂ (GeneralLinear C F.Carrier) W0)
    (τ1 : Representation ℂ (GeneralLinear A F.Carrier) W1)
    (τ2 : Representation ℂ (GeneralLinear B F.Carrier) W2),
    let := F.canonicalTopologicalData.topology
    IsSmooth τ0 → IsSmooth τ1 → IsSmooth τ2 →
    let τ12 := F.canonicalNormalizedProductInduced
      (twoBlocks A B hA hB) (pairFamily τ1 τ2)
    let left := F.canonicalNormalizedProductInduced
      (twoBlocks C (A + B) hC (Nat.add_pos_left hA B)) (pairFamily τ0 τ12)
    let τ01 := F.canonicalNormalizedProductInduced
      (twoBlocks C A hC hA) (pairFamily τ0 τ1)
    let right := F.canonicalNormalizedProductInduced
      (twoBlocks (C + A) B (Nat.add_pos_left hC A) hB) (pairFamily τ01 τ2)
    let rankTransport := GeneralLinear.reindex (R := F.Carrier)
      (finCongr (Nat.add_assoc C A B))
    Nonempty (Representation.Equiv (left.comp rankTransport.toMonoidHom) right)

/-- A common-universe proof yields the unchanged literal heterogeneous target. -/
theorem threeBlockInductionAssociativity_of_common
    (common : CommonUniverseThreeBlockAssociativity.{uF,max uV0 uV1 uV2}) :
    ThreeBlockInductionAssociativityStatement.{uF,uV0,uV1,uV2} := by
  intro p hp F C A B hC hA hB V0 _ _ V1 _ _ V2 _ _ ρ0 ρ1 ρ2
  let := F.canonicalTopologicalData.topology
  intro hρ0 hρ1 hρ2
  let τ0 := universeLiftRepresentation.{max uF uV0 uV1 uV2} ρ0
  let τ1 := universeLiftRepresentation.{max uF uV0 uV1 uV2} ρ1
  let τ2 := universeLiftRepresentation.{max uF uV0 uV1 uV2} ρ2
  have hτ0 : IsSmooth τ0 := (isSmooth_universeLift_iff.{max uF uV0 uV1 uV2} ρ0).mpr hρ0
  have hτ1 : IsSmooth τ1 := (isSmooth_universeLift_iff.{max uF uV0 uV1 uV2} ρ1).mpr hρ1
  have hτ2 : IsSmooth τ2 := (isSmooth_universeLift_iff.{max uF uV0 uV1 uV2} ρ2).mpr hρ2
  let H := common p F C A B hC hA hB τ0 τ1 τ2 hτ0 hτ1 hτ2
  let e := Classical.choice H
  let E := F.heterogeneousAssociativityEquiv.{uF,uV0,uV1,uV2,max uV0 uV1 uV2}
    hC hA hB
    (universeLiftEquiv.{max uF uV0 uV1 uV2} ρ0)
    (universeLiftEquiv.{max uF uV0 uV1 uV2} ρ1)
    (universeLiftEquiv.{max uF uV0 uV1 uV2} ρ2) e
  exact ⟨E⟩

end Langlands.Parabolic
