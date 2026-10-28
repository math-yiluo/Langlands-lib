import Langlands.Representation.RankinSelberg.InducedTailIntermediateDisintegrationAdapters

/-! # Specializing actual disintegration to the intermediate-tail chart -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear QuotientIntegration MeasureTheory HarmonicAnalysis
open scoped ENNReal

universe uF

section Data

variable {F : Type uF} [Field F] [TopologicalSpace F]

local instance : MeasurableSpace F := borel F
local instance (r : ℕ) : MeasurableSpace (LeftUnipotentQuotient r F) := borel _
local instance (r : ℕ) : MeasurableSpace (lowerTriangularSubgroup r F) := borel _

/-- Actual triangular measure and positive normalization, with the complete
integrability and integral transfer law in the intermediate-tail convention. -/
structure DisintegrationData (n d : ℕ) (abv : AbsoluteValue F ℝ)
    (μtail : Measure (LeftUnipotentQuotient n F))
    (μfull : Measure (LeftUnipotentQuotient (n + d) F))
    (dx : Measure (Matrix (Fin d) (Fin (n + 1)) F)) where
  triangularMeasure : Measure (lowerTriangularSubgroup d F)
  regular : triangularMeasure.Regular
  sigmaFinite : SigmaFinite triangularMeasure
  openPos : triangularMeasure.IsOpenPosMeasure
  finiteOnCompacts : IsFiniteMeasureOnCompacts triangularMeasure
  rightInvariant : triangularMeasure.IsMulRightInvariant
  normalization : ℝ
  normalization_pos : 0 < normalization
  transfer : ∀ f : LeftUnipotentQuotient (n + d) F → ℂ, Measurable f →
    (Integrable f μfull ↔
      Integrable (f ∘ quotientChart n d)
        ((μtail.withDensity (quotientDensity abv n d)).prod
          (dx.prod triangularMeasure))) ∧
    (Integrable f μfull →
      ∫ q, f q ∂μfull =
        (normalization : ℂ) * ∫ z, f (quotientChart n d z)
          ∂(μtail.withDensity (quotientDensity abv n d)).prod
            (dx.prod triangularMeasure))

end Data

private theorem quotientMeasureRankCast_symm {F : Type uF} [Field F]
    [TopologicalSpace F] {m n : ℕ} (h : m = n)
    (μ : @Measure (LeftQuotient (upperUnipotent m F))
      (borel (LeftQuotient (upperUnipotent m F)))) :
    quotientMeasureRankCast h.symm (quotientMeasureRankCast h μ) = μ := by
  subst n
  rfl

private theorem unipotentHaar_rightInvariant_of_index_eq
    {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F] {m n : ℕ} (h : m = n) :
    letI := borel (upperUnipotent (m + 1) F)
    letI : BorelSpace (upperUnipotent (m + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    Measure.IsMulRightInvariant (unipotentHaar F m) →
      Measure.IsMulRightInvariant (unipotentHaar F n) := by
  subst n
  exact id

/-- The exact published disintegration proposition supplies the transfer
premise used by the intermediate-tail calculation. Its proof remains an
explicit input; all quotient measures and the positive scalar are retained. -/
theorem disintegration_transfer_of_statement
    (hdis : LowerBlockQuotientDisintegrationStatement.{uF})
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n k : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + (k + 1) + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + (k + 1) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + (k + 1) + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + (k + 1) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (n + (k + 1)) F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient (n + (k + 1)) F.Carrier) := ⟨rfl⟩
    letI := borel (lowerTriangularSubgroup (k + 1) F.Carrier)
    letI : BorelSpace (lowerTriangularSubgroup (k + 1) F.Carrier) := ⟨rfl⟩
    ∀ (η : AdditiveHaarMeasure F.Carrier)
      [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (n + (k + 1)))]
      (μtail : Measure (LeftUnipotentQuotient n F.Carrier))
      (μfull : Measure (LeftUnipotentQuotient (n + (k + 1)) F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μtail →
      IsCompatible (upperUnipotent (n + (k + 1) + 1) F.Carrier)
        (generalLinearHaar F.Carrier (n + (k + 1)))
        (unipotentHaar F.Carrier (n + (k + 1))) μfull →
      ∃ ρ : Measure (lowerTriangularSubgroup (k + 1) F.Carrier),
        ρ.Regular ∧ SigmaFinite ρ ∧ ρ.IsOpenPosMeasure ∧
        IsFiniteMeasureOnCompacts ρ ∧ ρ.IsMulRightInvariant ∧
        ∃ C : ℝ, 0 < C ∧
          ∀ f : LeftUnipotentQuotient (n + (k + 1)) F.Carrier → ℂ, Measurable f →
            (Integrable f μfull ↔
              Integrable (f ∘ quotientChart n (k + 1))
                ((μtail.withDensity
                  (quotientDensity (normalizedAbsoluteValue F.canonicalTopologicalData)
                    n (k + 1))).prod
                    ((rectangularMeasure η (k + 1) (n + 1)).prod ρ))) ∧
            (Integrable f μfull →
              ∫ q, f q ∂μfull =
                (C : ℂ) * ∫ z, f (quotientChart n (k + 1) z)
                  ∂(μtail.withDensity
                    (quotientDensity (normalizedAbsoluteValue F.canonicalTopologicalData)
                      n (k + 1))).prod
                      ((rectangularMeasure η (k + 1) (n + 1)).prod ρ)) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + (k + 1) + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + (k + 1) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + (k + 1) + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + (k + 1) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (n + (k + 1)) F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient (n + (k + 1)) F.Carrier) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup (k + 1) F.Carrier)
  let : BorelSpace (lowerTriangularSubgroup (k + 1) F.Carrier) := ⟨rfl⟩
  intro η hrightTail hrightFull μtail μfull htail hfull
  have hi : n + 1 + k = n + (k + 1) := by omega
  let := borel (Langlands.GeneralLinear (n + 1 + k + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1 + k + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1 + k + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1 + k + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (n + 1 + k) F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient (n + 1 + k) F.Carrier) := ⟨rfl⟩
  let : Measure.IsMulRightInvariant (unipotentHaar F.Carrier (n + 1 + k)) :=
    unipotentHaar_rightInvariant_of_index_eq hi.symm hrightFull
  let μraw := quotientMeasureRankCast (congrArg (· + 1) hi.symm) μfull
  have hraw : IsCompatible (upperUnipotent (n + 1 + k + 1) F.Carrier)
      (generalLinearHaar F.Carrier (n + 1 + k))
      (unipotentHaar F.Carrier (n + 1 + k)) μraw :=
    (compatible_quotientMeasureRankCast_iff hi.symm μfull).2 hfull
  rcases hdis p F n k η μtail μraw htail hraw with
    ⟨_, _, _, _, ρ, hreg, hσ, hpos, hfc, hright, _, C, hC, _, htransfer⟩
  refine ⟨ρ, hreg, hσ, hpos, hfc, hright, C, hC, ?_⟩
  intro f hf
  let hr := congrArg (· + 1) hi
  let fraw := f ∘ upperUnipotentQuotientCongr hr
  have hfraw : Measurable fraw :=
    (measurable_comp_upperUnipotentQuotientCongr hr f).2 hf
  obtain ⟨hiff, hint⟩ := htransfer fraw hfraw
  have hμ : quotientMeasureRankCast hr μraw = μfull :=
    quotientMeasureRankCast_symm (congrArg (· + 1) hi.symm) μfull
  have hifull : Integrable f μfull ↔ Integrable fraw μraw := by
    simpa only [hμ] using integrable_quotientMeasureRankCast_iff hr μraw f
  have hifullIntegral : ∫ q, f q ∂μfull = ∫ q, fraw q ∂μraw := by
    simpa only [hμ, fraw, Function.comp_def] using
      integral_quotientMeasureRankCast hr μraw f
  have hchart : fraw ∘ lowerBlockQuotientChart (a := n + 1) (d := k + 1) =
      f ∘ quotientChart n (k + 1) := rfl
  rw [← quotientDensity_eq_lowerBlockQuotientDensity] at hiff hint
  refine ⟨?_, ?_⟩
  · simpa only [hchart] using hifull.trans hiff
  · intro hfi
    rw [hifullIntegral, hint (hifull.mp hfi)]
    rfl

/-- Choose actual disintegration data from the exact disintegration premise,
retaining the supplied compatible measures and additive Haar input. -/
def disintegrationDataOfStatement
    (hdis : LowerBlockQuotientDisintegrationStatement.{uF})
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (n k : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + (k + 1) + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + (k + 1) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + (k + 1) + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + (k + 1) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (n + (k + 1)) F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient (n + (k + 1)) F.Carrier) := ⟨rfl⟩
    letI := borel (lowerTriangularSubgroup (k + 1) F.Carrier)
    letI : BorelSpace (lowerTriangularSubgroup (k + 1) F.Carrier) := ⟨rfl⟩
    ∀ (η : AdditiveHaarMeasure F.Carrier)
      [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (n + (k + 1)))]
      (μtail : Measure (LeftUnipotentQuotient n F.Carrier))
      (μfull : Measure (LeftUnipotentQuotient (n + (k + 1)) F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μtail →
      IsCompatible (upperUnipotent (n + (k + 1) + 1) F.Carrier)
        (generalLinearHaar F.Carrier (n + (k + 1)))
        (unipotentHaar F.Carrier (n + (k + 1))) μfull →
      DisintegrationData n (k + 1)
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        μtail μfull (rectangularMeasure η (k + 1) (n + 1)) := by
  classical
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + (k + 1) + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + (k + 1) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + (k + 1) + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + (k + 1) + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (n + (k + 1)) F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient (n + (k + 1)) F.Carrier) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup (k + 1) F.Carrier)
  let : BorelSpace (lowerTriangularSubgroup (k + 1) F.Carrier) := ⟨rfl⟩
  intro η hrightTail hrightFull μtail μfull htail hfull
  choose ρ hreg hσ hpos hfc hright C hC htransfer using
    disintegration_transfer_of_statement hdis p F n k η μtail μfull htail hfull
  exact ⟨ρ, hreg, hσ, hpos, hfc, hright, C, hC, htransfer⟩

end Langlands.RankinSelberg.InducedTailIntermediate
