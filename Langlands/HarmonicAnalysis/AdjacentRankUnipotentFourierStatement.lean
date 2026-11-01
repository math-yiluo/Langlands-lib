import Langlands.Representation.RankinSelberg.AdjacentRankStarData
import Langlands.Representation.RankinSelberg.Measures

/-! Source-derived scalar Fourier identity from JPSS Section 6.2, formula (2).
This is a proposition definition, not a proof. -/

noncomputable section

namespace Langlands.HarmonicAnalysis

open MeasureTheory GeneralLinear RankinSelberg Whittaker

universe uF

/-- The actual rectangular unipotent Fourier identity, retaining both
absolute convergence assertions. The group Haar is the shared normalized
unipotent Haar, while all additive Fourier measures use the supplied self-dual
scalar Haar. No model or representation coefficient occurs in this statement. -/
def AdjacentRankUnipotentFourierStatement : Prop :=
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
      (ν : AdditiveHaarMeasure F.Carrier) (hself : IsSelfDual ψ ν) (r : ℕ),
      letI : MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
      haveI : BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
      ∀ (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)),
        let w := weylLong (r + 1) F.Carrier
        let ε := adjacentRankEpsilon F.Carrier r
        let T := partialFourierEquiv ψ ν (r + 1) hself
        let L : upperUnipotent (r + 1) F.Carrier → ℂ := fun n =>
          T (rectangularTranslate
            (weylLong (r + 2) F.Carrier * adjacentRankZeta F.Carrier r) Φ)
            (rectangularJoin n.val.val ε) *
              (inverseStandardCharacter ψ r n : ℂ)
        let R : upperUnipotent (r + 1) F.Carrier → ℂ := fun n =>
          rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself (T Φ)
            (rectangularJoin (w.val * n.val.val) (Matrix.mulVec w.val ε)) *
              (standardCharacter ψ r n : ℂ)
        Integrable L (unipotentHaar F.Carrier r) ∧
          Integrable R (unipotentHaar F.Carrier r) ∧
          (∫ n, L n ∂unipotentHaar F.Carrier r) =
            ∫ n, R n ∂unipotentHaar F.Carrier r

end Langlands.HarmonicAnalysis
