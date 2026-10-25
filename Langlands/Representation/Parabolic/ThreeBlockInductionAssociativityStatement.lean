import Langlands.Representation.Shahidi.Induction
import Mathlib.Algebra.Module.ULift

/-!
# Heterogeneous three-block associativity for normalized upper induction

An internal statement specialization of ordered normalized induction in stages,
motivated by the two groupings in JPSS (1983), §9.3, printed page 457.
The four induction nodes use the literal heterogeneous carrier convention of
`Langlands.RankinSelberg.InducedTailLFactorStatement`.
-/

noncomputable section

namespace Langlands.Parabolic

universe uF uV0 uV1 uV2

/-- The two bracketings of three smooth factors are equivalent after the explicit
coordinate-preserving ambient rank cast. All factors and the field have independent
universes. This definition states associativity; it does not prove it. -/
def ThreeBlockInductionAssociativityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (C A B : ℕ) (hC : 0 < C) (hA : 0 < A) (hB : 0 < B)
    {V0 : Type uV0} [AddCommGroup V0] [Module ℂ V0]
    {V1 : Type uV1} [AddCommGroup V1] [Module ℂ V1]
    {V2 : Type uV2} [AddCommGroup V2] [Module ℂ V2]
    (ρ0 : Representation ℂ (GeneralLinear C F.Carrier) V0)
    (ρ1 : Representation ℂ (GeneralLinear A F.Carrier) V1)
    (ρ2 : Representation ℂ (GeneralLinear B F.Carrier) V2),
    letI := F.canonicalTopologicalData.topology
    IsSmooth ρ0 → IsSmooth ρ1 → IsSmooth ρ2 →
    let ρ1L : Representation ℂ (GeneralLinear A F.Carrier) (ULift.{uV2} V1) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ1
    let ρ2L : Representation ℂ (GeneralLinear B F.Carrier) (ULift.{uV1} V2) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ2
    let ρ12 := F.canonicalNormalizedProductInduced
      (Shahidi.twoBlocks A B hA hB) (Shahidi.pairFamily ρ1L ρ2L)
    let ρ0L : Representation ℂ (GeneralLinear C F.Carrier)
        (ULift.{max uF uV1 uV2} V0) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ0
    let ρ12L : Representation ℂ (GeneralLinear (A + B) F.Carrier) (ULift.{uV0} _) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ12
    let left := F.canonicalNormalizedProductInduced
      (Shahidi.twoBlocks C (A + B) hC (Nat.add_pos_left hA B))
      (Shahidi.pairFamily ρ0L ρ12L)
    let ρ0R : Representation ℂ (GeneralLinear C F.Carrier) (ULift.{uV1} V0) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ0
    let ρ1R : Representation ℂ (GeneralLinear A F.Carrier) (ULift.{uV0} V1) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ1
    let ρ01 := F.canonicalNormalizedProductInduced
      (Shahidi.twoBlocks C A hC hA) (Shahidi.pairFamily ρ0R ρ1R)
    let ρ01R : Representation ℂ (GeneralLinear (C + A) F.Carrier) (ULift.{uV2} _) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ01
    let ρ2R : Representation ℂ (GeneralLinear B F.Carrier)
        (ULift.{max uF uV0 uV1} V2) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp ρ2
    let right := F.canonicalNormalizedProductInduced
      (Shahidi.twoBlocks (C + A) B (Nat.add_pos_left hC A) hB)
      (Shahidi.pairFamily ρ01R ρ2R)
    let rankTransport : GeneralLinear ((C + A) + B) F.Carrier ≃*
        GeneralLinear (C + (A + B)) F.Carrier :=
      GeneralLinear.reindex (R := F.Carrier) (finCongr (Nat.add_assoc C A B))
    Nonempty (Representation.Equiv (left.comp rankTransport.toMonoidHom) right)

end Langlands.Parabolic
