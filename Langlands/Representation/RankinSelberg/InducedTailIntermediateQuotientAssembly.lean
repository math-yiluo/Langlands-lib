import Langlands.Representation.RankinSelberg.InducedTailIntermediateQuotientPointwise
import Langlands.Representation.RankinSelberg.InducedTailIntermediateIntegralAssembly
import Langlands.Representation.RankinSelberg.UnequalRankZeroRowIntegrandContinuityProof

/-! # Actual quotient-to-span assembly for the intermediate tail -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear MeasureTheory Whittaker HarmonicAnalysis
open scoped ENNReal

universe uF uV uW

/-- The published zero-row continuity theorem applies to arbitrary members
of the actual coefficient images, without a choice of Whittaker functional. -/
theorem continuous_zeroRow_integrand_of_mem
    {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (habv : Continuous abv) (n k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {E : Type uW} [AddCommGroup E] [Module ℂ E]
    (π : Representation ℂ (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) E)
    (hπ : IsSmooth π) (hσ : IsSmooth σ)
    {W : WhittakerFunctions ψ (n + (0 + k + 1))}
    (hW : W ∈ whittakerSet ψ _ π)
    {W' : InverseWhittakerFunctions ψ n} (hW' : W' ∈ inverseWhittakerSet ψ n σ)
    (s : ℂ) :
    Continuous (unequalRankIntegrand ψ abv 0 k W W' s 0) := by
  obtain ⟨ℓ, hW⟩ := hW
  obtain ⟨ℓ', hW'⟩ := hW'
  exact unequalRankZeroRowIntegrandContinuous F n k abv habv
    V E π σ hπ hσ ψ ℓ ℓ' ⟨W, hW⟩ ⟨W', hW'⟩ s

/-- A diagonal extension and the actual lower-block measure transfer put a
reversed-tail rational continuation in the actual full Laurent span. All
extension, full-type and measure-transfer hypotheses remain explicit. -/
theorem mem_full_zetaSpan_of_diagonal_extension
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (n d c₀ k : ℕ) (hd : d = k + 1) :
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
              Integrable (f ∘ quotientChart n d)
                ((μtail.withDensity
                  (quotientDensity (normalizedAbsoluteValue F.canonicalTopologicalData) n d)).prod
                    (dx.prod ρ))) ∧
            (Integrable f μfull →
              ∫ q, f q ∂μfull =
                (C : ℂ) * ∫ z, f (quotientChart n d z)
                  ∂(μtail.withDensity
                    (quotientDensity (normalizedAbsoluteValue F.canonicalTopologicalData) n d)).prod
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
              σ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.valuativeExtension
  let := F.canonicalTopologicalData.moduleTopology
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (n + d) F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient (n + d) F.Carrier) := ⟨rfl⟩
  let := borel (lowerTriangularSubgroup d F.Carrier)
  let : BorelSpace (lowerTriangularSubgroup d F.Carrier) := ⟨rfl⟩
  intro ψ V _ _ π hπ Wtail E _ _ σ hσ Wtest hWtest hext
    μtail _ μfull dx _ _ _ ρ _ _ _ C hC htransfer g R a hg hR
  obtain ⟨Ω₁, Ω₂, hΩ₁c, hΩ₁o, hΩ₂c, hΩ₂o, W₀, hW₀, hpt⟩ :=
    exists_localized_quotient_integrand_comparison p F n d c₀ k hd
      ψ V π hπ Wtail E σ hσ Wtest hWtest hext
  have hRank : n + 1 + d + c₀ = (n + d) + (0 + c₀ + 1) := by omega
  let π' := hRank ▸ (show Representation ℂ
    (Langlands.GeneralLinear ((n + 1 + d + c₀) + 1) F.Carrier) V from π)
  let Wf := whittakerRankCast ψ hRank W₀
  have hWf : Wf ∈ whittakerSet ψ _ π' := whittakerRankCast_mem ψ hRank π hW₀
  have hπ' : IsSmooth π' := representationRankCast_isSmooth hRank π hπ.1.1
  have habv : Continuous (normalizedAbsoluteValue F.canonicalTopologicalData) :=
    NNReal.continuous_coe.comp F.canonicalTopologicalData.continuous_normalizedAbsHom
  apply mem_zetaSpan_of_localized_disintegration
    F.canonicalTopologicalData.residueCardinality ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData) c₀ μfull hWf hWtest
    μtail dx ρ (quotientChart n d)
    (measurable_quotientDensity _ habv n d)
    (quotientDensity_ne_top _ n d) hC
    hΩ₁o.measurableSet hΩ₂o.measurableSet
    (compactOpen_volume_pos dx hΩ₁c hΩ₁o ⟨0, Ω₁.zero_mem⟩)
    (compactOpen_volume_pos ρ hΩ₂c hΩ₂o ⟨1, Ω₂.one_mem⟩) g a
  · intro s _
    exact htransfer _ (continuous_zeroRow_integrand_of_mem
      ψ _ habv (n + d) c₀ π' σ hπ' hσ hWf hWtest s).measurable
  · intro s _ q x h
    exact hpt q x h s 0 0
  · exact hg
  · exact hR

end Langlands.RankinSelberg.InducedTailIntermediate
