import Langlands.Group.GL.LowerBlockQuotientCoordinates
import Langlands.Representation.RankinSelberg.InducedTailIntermediateCoefficientAdapters
import Langlands.Representation.RankinSelberg.WhittakerNormData
import Langlands.Representation.RankinSelberg.InducedTailSpanStatement

/-! # Conditional intermediate-tail span from diagonal extension and disintegration -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear MeasureTheory Whittaker HarmonicAnalysis InducedTailIntermediate
open scoped ENNReal

universe uF uV uW

/-- A diagonal extension, full Whittaker type and the actual lower-block
measure transfer imply the span conclusion for a reversed-character tail
continuation. This proposition retains all three prerequisites explicitly. -/
def InducedTailIntermediateDiagonalExtensionSpanStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (n d c₀ k : ℕ) (hd : d = k + 1),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.valuativeExtension
    letI := F.canonicalTopologicalData.moduleTopology
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (n + d) F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient (n + d) F.Carrier) := ⟨rfl⟩
    letI := borel (lowerTriangularSubgroup d F.Carrier)
    letI : BorelSpace (lowerTriangularSubgroup d F.Carrier) := ⟨rfl⟩
    let chart : LeftUnipotentQuotient n F.Carrier ×
        (Matrix (Fin d) (Fin (n + 1)) F.Carrier ×
          lowerTriangularSubgroup d F.Carrier) →
        LeftUnipotentQuotient (n + d) F.Carrier :=
      fun z => upperUnipotentQuotientCongr
        (by omega : (n + 1) + d = (n + d) + 1) (lowerBlockQuotientChart z)
    let D : LeftUnipotentQuotient n F.Carrier → ℝ≥0∞ :=
      fun q => ENNReal.ofReal (quotientDeterminantAbs
        (normalizedAbsoluteValue F.canonicalTopologicalData) n q ^ (-(d : ℤ)))
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ
        (Langlands.GeneralLinear ((n + 1) + d + (c₀ + 1)) F.Carrier) V),
      IsOfWhittakerType (n + 1 + d + c₀)
        (standardCharacter ψ (n + 1 + d + c₀)) π →
      ∀ (Wtail : WhittakerFunctions ψ n)
        (E : Type uW) [AddCommGroup E] [Module ℂ E]
        (σ : Representation ℂ
          (Langlands.GeneralLinear (n + d + 1) F.Carrier) E),
        IsSmooth σ →
        ∀ Wtest ∈ inverseWhittakerSet ψ (n + d) σ,
          (∀ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier),
            ∃ W ∈ whittakerSet ψ (n + 1 + d + c₀) π,
              ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
                W.val (lowerBlockLocalization (c₀ + 1) g 0 1) =
                  Wtail.val g * Φ (lastRow g) *
                    (Real.rpow
                      (F.canonicalTopologicalData.normalizedAbs (Matrix.det g.val))
                      (((d + (c₀ + 1) : ℕ) : ℝ) / 2) : ℂ)) →
          ∀ (μtail : Measure (LeftUnipotentQuotient n F.Carrier)) [SFinite μtail]
            (μfull : Measure (LeftUnipotentQuotient (n + d) F.Carrier))
            (dx : Measure (Matrix (Fin d) (Fin (n + 1)) F.Carrier)) [SFinite dx]
            [dx.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts dx]
            (ρ : Measure (lowerTriangularSubgroup d F.Carrier)) [SFinite ρ]
            [ρ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ρ]
            (C : ℝ), 0 < C →
          (∀ f : LeftUnipotentQuotient (n + d) F.Carrier → ℂ, Measurable f →
            (Integrable f μfull ↔
              Integrable (f ∘ chart)
                ((μtail.withDensity
                  D).prod
                    (dx.prod ρ))) ∧
            (Integrable f μfull →
              ∫ q, f q ∂μfull =
                (C : ℂ) * ∫ z, f (chart z)
                  ∂(μtail.withDensity
                    D).prod
                      (dx.prod ρ))) →
          let g := fun s : ℂ => unequalRankIntegrand (ψ.scale (-1))
            (normalizedAbsoluteValue F.canonicalTopologicalData) 0 k
            (inverseAsScaledStandard ψ
              (inverseWhittakerRankCast ψ
                (by omega : n + d = n + (0 + k + 1)) Wtest))
            (standardAsScaledInverse ψ Wtail) s 0
          ∀ (R : RationalFunctions) (a : ℝ),
            (∀ s : ℂ, a < s.re → Integrable (g s) μtail) →
            HasRationalContinuation F.canonicalTopologicalData.residueCardinality
              (fun s => ∫ q, g s q ∂μtail) R →
            R ∈ zetaSpan (unequalRankZetaValues
              F.canonicalTopologicalData.residueCardinality ψ
              (normalizedAbsoluteValue F.canonicalTopologicalData) 0 c₀
              μfull (Measure.dirac 0)
              ((by omega : n + 1 + d + c₀ = (n + d) + (0 + c₀ + 1)) ▸
                (show Representation ℂ
                  (Langlands.GeneralLinear ((n + 1 + d + c₀) + 1) F.Carrier) V from π))
              σ)

end Langlands.RankinSelberg
