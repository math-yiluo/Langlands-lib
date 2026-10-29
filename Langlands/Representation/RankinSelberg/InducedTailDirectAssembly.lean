import Langlands.Representation.RankinSelberg.InducedTailSpanStatement
import Langlands.Representation.RankinSelberg.LaurentDivisibilityProof

/-!
# Conditional assembly of the three direct tail-divisibility cases

This support module takes the three Laurent-span statements and certified
factor witnesses as explicit inputs. It does not prove their existence or the
parent tail-divisibility statement.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial

universe uF uV₁ uV₂ uW

/-- Conditional direct-rank assembly, with the actual parent induction and
independent quotient measures. The analytic span statements and certified
polynomial witnesses remain explicit hypotheses of this helper. -/
theorem inducedTailDirectPolynomialDivisibility_of_spans
    (hspans : InducedTailSpanStatement.{uF, uV₁, uV₂, uW})
    (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (a b t : ℕ)
    {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (hπ₁ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) π₁)
    (hπ₂ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType b (standardCharacter ψ b) π₂)
    (hσ : letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ)
    (hTr : t + 1 < (a + 1) + (b + 1))
    (Pfull Ptail : ℂ[X])
    (hfull :
      let π₁' : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)
          (ULift.{uV₂} V₁) :=
        (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
      let π₂' : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier)
          (ULift.{uV₁} V₂) :=
        (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
      IsPadicSymmetricLPolynomial F ψ ν.val
        (F.canonicalNormalizedProductInduced
          (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
          (Shahidi.pairFamily π₁' π₂')) σ Pfull)
    (htail : IsPadicSymmetricLPolynomial F ψ ν.val π₂ σ Ptail) :
    Ptail ∣ Pfull := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (b + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (b + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (b + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (b + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient b F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient b F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
  let π₁' : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)
      (ULift.{uV₂} V₁) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
  let π₂' : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier)
      (ULift.{uV₁} V₂) :=
    (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
  let ξ := F.canonicalNormalizedProductInduced
    (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
    (Shahidi.pairFamily π₁' π₂')
  change IsPadicSymmetricLPolynomial F ψ ν.val ξ σ Pfull at hfull
  have hfullPair := (isPadicSymmetricLPolynomial_of_le
    (show t ≤ a + 1 + b by omega)).1 hfull
  obtain ⟨hRt, μfull, hμfull⟩ := hfullPair.1
  let := hRt
  have hgenFull := (isPairLPolynomial_of_lt (show t < a + 1 + b by omega)).1
    (hfullPair.2 μfull hμfull) 0 (a + 1 + b - t - 1)
      (show a + 1 + b = t + (0 + (a + 1 + b - t - 1) + 1) by omega)
  rcases lt_trichotomy t b with htb | htb | hbt
  · have htailPair := (isPadicSymmetricLPolynomial_of_le (by omega)).1 htail
    obtain ⟨_, μtail, hμtail⟩ := htailPair.1
    have hgenTail := (isPairLPolynomial_of_lt htb).1
      (htailPair.2 μtail hμtail) 0 (b - t - 1) (by omega)
    have hspan := hspans.2.1 p F ψ ν a b t π₁ π₂ σ hπ₁ hπ₂ hσ
      (by omega) μtail μfull hμtail hμfull
    exact (normalizedGeneratorSpanDivisibility _ _ Ptail Pfull hgenTail hgenFull).1 hspan
  · subst t
    have htailPair := (isPadicSymmetricLPolynomial_of_le le_rfl).1 htail
    obtain ⟨_, μtail, hμtail⟩ := htailPair.1
    have hgenTail := isPairLPolynomial_self.1 (htailPair.2 μtail hμtail)
    have hspan := hspans.1 p F ψ ν a b b π₁ π₂ σ hπ₁ hπ₂ hσ
      rfl μtail μfull hμtail hμfull
    exact (normalizedGeneratorSpanDivisibility _ _ Ptail Pfull hgenTail hgenFull).1 hspan
  · have htailPair := (isPadicSymmetricLPolynomial_of_lt hbt).1 htail
    obtain ⟨hRb, μtail, hμtail⟩ := htailPair.1
    let := hRb
    have hgenTail := (isPairLPolynomial_of_lt hbt).1
      (htailPair.2 μtail hμtail) 0 (t - b - 1) (by omega)
    have hspan := hspans.2.2 p F ψ ν a b t π₁ π₂ σ hπ₁ hπ₂ hσ
      (by omega) hTr μtail μfull hμtail hμfull
    exact (normalizedGeneratorSpanDivisibility _ _ Ptail Pfull hgenTail hgenFull).1 hspan

end Langlands.RankinSelberg
