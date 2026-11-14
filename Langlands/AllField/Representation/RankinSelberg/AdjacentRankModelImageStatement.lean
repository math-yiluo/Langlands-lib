import Langlands.Representation.RankinSelberg.AdjacentRankModelImageStatement
import Langlands.AllField.Representation.Induction.OppositeParabolic
import Langlands.AllField.Representation.RankinSelberg.AdjacentRankIntegralModel
import Langlands.AllField.Representation.RankinSelberg.RankOneExtensionCharacter
import Langlands.AllField.Representation.Shahidi.Induction
/-!
# Large-second-twist image equality for the JPSS adjacent-rank model

The literal Section 6.1 integral has, for all sufficiently large real twists
of the second lower block, the same image as the coefficients of one nonzero
Whittaker functional on the actual normalized opposite parabolic induction.
This module defines an unproved, source-derived proposition.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding AdjacentRankModelImageStatement EqualRankAnalyticStatement QuotientHaarExistenceStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacter_isOfWhittakerType rankOneExtensionCharacter rankOneExtensionCharacter_isOfWhittakerType rankOneExtensionCharacter_isSmooth rankOneWhittakerType
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding PadicMatrixFourierSliceStatement PadicRowFourierSurjectivityStatement padicMatrixFourierSlice padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr

universe uF uV

/-- The large-positive-second-twist image assertion of JPSS Section 6.1,
formula (8), retaining the original full Whittaker-type representation as
the first inducing block. The bound is uniform over all test tensors, and
the same nonzero induced functional supplies every coefficient in the image.
This is a proposition definition, with the original-carrier transport and
the analytic and spanning arguments left to a later proof. -/
def AdjacentRankModelImageStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI : MeasurableSpace F := borel F
    haveI : BorelSpace F := ⟨rfl⟩
    haveI : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
    haveI : TotallyDisconnectedSpace F := by
      let : NonarchimedeanRing F := by
        convert! ValuativeRel.nonarchimedeanRing F
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F)
      (ν : AdditiveHaarMeasure F) (hself : IsSelfDual ψ ν)
      (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V],
      letI := (⟨⟩ : LocalFieldData F).generalLinearTopology (r + 1)
      haveI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (r + 1)
      letI := (⟨⟩ : LocalFieldData F).generalLinearTopology (r + 2)
      haveI := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup (r + 2)
      ∀ (σ : Representation ℂ (GeneralLinear (r + 1) F) V),
        IsOfWhittakerType r (standardCharacter ψ r) σ →
        ∀ (ℓ : glFunctionals ψ r σ), ℓ.val ≠ 0 →
          ∀ (χ₀ : Quasicharacter F),
            ∃ C : ℝ, ∀ u : ℝ, C < u →
              let χᵤ : Quasicharacter F :=
                χ₀ * (⟨⟩ : LocalFieldData F).unramifiedCharacterContinuous
                  (LocalFactor.spectralParameter
                    (⟨⟩ : LocalFieldData F).residueCardinality
                    (⟨⟩ : LocalFieldData F).residueCardinality_real_pos (u : ℂ))
              let B := Shahidi.twoBlocks (r + 1) 1 (Nat.succ_pos r) (Nat.succ_pos 0)
              let ρᵤ := (⟨⟩ : LocalFieldData F).normalizedOppositeParabolicInduced B
                (B.blockTensor (Shahidi.pairFamily σ
                  (rankOneExtensionCharacter.{uF, uV} F χᵤ)))
              ∃ J : glFunctionals ψ (r + 1) ρᵤ, J.val ≠ 0 ∧
                Set.range (fun Ψ : adjacentRankTestSpace ψ σ ℓ =>
                  fun g => Langlands.AllField.RankinSelberg.Padic.adjacentRankModelIntegral F ψ ν hself σ ℓ χᵤ Ψ g) =
                Set.range (fun v : ρᵤ.asModule => fun g => J.val (ρᵤ g v))

end Langlands.AllField.RankinSelberg
