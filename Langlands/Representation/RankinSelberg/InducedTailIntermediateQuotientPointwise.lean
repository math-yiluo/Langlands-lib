import Langlands.Representation.RankinSelberg.InducedTailIntermediatePointwise
import Langlands.Representation.RankinSelberg.InducedTailIntermediateQuotientData

/-! # Localized comparison on the actual JPSS quotient -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear Whittaker HarmonicAnalysis Topology

universe uF uV uW

/-- The localized actual-integrand identity descends to every small quotient
point with the intrinsic determinant density. Extension and full Whittaker
type remain explicit hypotheses. -/
theorem exists_localized_quotient_integrand_comparison
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (n d c₀ k : ℕ) (hd : d = k + 1) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.valuativeExtension
    letI := F.canonicalTopologicalData.moduleTopology
    letI := F.canonicalTopologicalData.localField
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
          ∃ Ω₁ : AddSubgroup (Matrix (Fin d) (Fin (n + 1)) F.Carrier),
            ∃ Ω₂ : Subgroup (lowerTriangularSubgroup d F.Carrier),
              IsCompact (Ω₁ : Set (Matrix (Fin d) (Fin (n + 1)) F.Carrier)) ∧
              IsOpen (Ω₁ : Set (Matrix (Fin d) (Fin (n + 1)) F.Carrier)) ∧
              IsCompact (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)) ∧
              IsOpen (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)) ∧
              ∃ W₀ ∈ whittakerSet ψ (n + 1 + d + c₀) π,
                ∀ (q : LeftUnipotentQuotient n F.Carrier)
                  (x : Matrix (Fin d) (Fin (n + 1)) F.Carrier)
                  (h : lowerTriangularSubgroup d F.Carrier) (s : ℂ)
                  (rFull : Matrix (Fin 0) (Fin (n + d + 1)) F.Carrier)
                  (rTail : Matrix (Fin 0) (Fin (n + 1)) F.Carrier),
                  unequalRankIntegrand ψ
                    (normalizedAbsoluteValue F.canonicalTopologicalData) 0 c₀
                    (whittakerRankCast ψ (by omega) W₀) Wtest s rFull
                    (quotientChart n d (q, (x, h))) *
                    ((quotientDensity
                      (normalizedAbsoluteValue F.canonicalTopologicalData) n d q).toReal : ℂ) =
                  unequalRankIntegrand (ψ.scale (-1))
                    (normalizedAbsoluteValue F.canonicalTopologicalData) 0 k
                    (inverseAsScaledStandard ψ
                      (inverseWhittakerRankCast ψ
                        (by omega : n + d = n + (0 + k + 1)) Wtest))
                    (standardAsScaledInverse ψ Wtail) s rTail q *
                    ((Ω₁ : Set (Matrix (Fin d) (Fin (n + 1)) F.Carrier)).indicator
                        (fun _ => (1 : ℂ)) x *
                      (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)).indicator
                        (fun _ => (1 : ℂ)) h) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.valuativeExtension
  let := F.canonicalTopologicalData.moduleTopology
  let := F.canonicalTopologicalData.localField
  intro ψ V _ _ π hπ Wtail E _ _ σ hσ Wtest hWtest hext
  obtain ⟨Ω₁, Ω₂, hΩ₁c, hΩ₁o, hΩ₂c, hΩ₂o, W₀, hW₀, hcomp⟩ :=
    exists_localized_integrand_comparison p F n d c₀ k hd
      ψ V π hπ Wtail E σ hσ Wtest hWtest hext
  refine ⟨Ω₁, Ω₂, hΩ₁c, hΩ₁o, hΩ₂c, hΩ₂o, W₀, hW₀, ?_⟩
  intro q x h s rFull rTail
  refine Quotient.inductionOn q ?_
  intro g
  simpa only [quotientChart_mk, quotientDensity_toReal,
    quotientDeterminantAbs_mk, normalizedAbsoluteValue_apply] using
      hcomp g x h s rFull rTail

end Langlands.RankinSelberg.InducedTailIntermediate
