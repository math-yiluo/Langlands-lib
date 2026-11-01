import Langlands.Representation.RankinSelberg.AdjacentRankIntegralModel
import Langlands.Representation.RankinSelberg.RankOneExtensionCharacter
import Langlands.Representation.Shahidi.Induction
import Langlands.Representation.Induction.OppositeParabolic

/-!
# Large-second-twist image equality for the JPSS adjacent-rank model

The literal Section 6.1 integral has, for all sufficiently large real twists
of the second lower block, the same image as the coefficients of one nonzero
Whittaker functional on the actual normalized opposite parabolic induction.
This module defines an unproved, source-derived proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker

universe uF uV

/-- The large-positive-second-twist image assertion of JPSS Section 6.1,
formula (8), retaining the original full Whittaker-type representation as
the first inducing block. The bound is uniform over all test tensors, and
the same nonzero induced functional supplies every coefficient in the image.
This is a proposition definition, with the original-carrier transport and
the analytic and spanning arguments left to a later proof. -/
def AdjacentRankModelImageStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    haveI : BorelSpace F.Carrier := ⟨rfl⟩
    haveI : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
    haveI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ν : AdditiveHaarMeasure F.Carrier) (hself : IsSelfDual ψ ν)
      (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V],
      letI := F.canonicalGeneralLinearTopology (r + 1)
      haveI := F.canonicalGeneralLinearTopologicalGroup (r + 1)
      letI := F.canonicalGeneralLinearTopology (r + 2)
      haveI := F.canonicalGeneralLinearTopologicalGroup (r + 2)
      ∀ (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V),
        IsOfWhittakerType r (standardCharacter ψ r) σ →
        ∀ (ℓ : glFunctionals ψ r σ), ℓ.val ≠ 0 →
          ∀ (χ₀ : Quasicharacter F.Carrier),
            ∃ C : ℝ, ∀ u : ℝ, C < u →
              let χᵤ : Quasicharacter F.Carrier :=
                χ₀ * F.canonicalTopologicalData.unramifiedCharacterContinuous
                  (LocalFactor.spectralParameter
                    F.canonicalTopologicalData.residueCardinality
                    F.canonicalTopologicalData.residueCardinality_real_pos (u : ℂ))
              let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
              let ρᵤ := F.canonicalNormalizedOppositeParabolicInduced B
                (B.blockTensor (Shahidi.pairFamily σ
                  (rankOneExtensionCharacter.{uF, uV} F χᵤ)))
              ∃ J : glFunctionals ψ (r + 1) ρᵤ, J.val ≠ 0 ∧
                Set.range (fun Ψ : adjacentRankTestSpace ψ σ ℓ =>
                  fun g => Padic.adjacentRankModelIntegral F ψ ν hself σ ℓ χᵤ Ψ g) =
                Set.range (fun v : ρᵤ.asModule => fun g => J.val (ρᵤ g v))

end Langlands.RankinSelberg
