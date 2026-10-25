import Langlands.Representation.RankinSelberg.InducedTailLFactorStatement

/-!
# Direct-rank Laurent-span inclusions for the tail of upper induction

The three direct cases in JPSS (9.3), printed 455–457, stated with the
literal canonical induction and actual rational zeta values. The paired
Markdown identifies the derived coordinate/measure and Whittaker-type scope.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV₁ uV₂ uW

/-- Tail and test ranks are equal (`T = B`); full and test ranks are unequal.
Every Schwartz row test is retained in the equal-rank tail value set. -/
def InducedTailEqualRankSpanStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (a b t : ℕ)
    {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) π₁) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType b (standardCharacter ψ b) π₂) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ) →
    let π₁' : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)
        (ULift.{uV₂} V₁) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
    let π₂' : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier)
        (ULift.{uV₁} V₂) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
    let ξ := F.canonicalNormalizedProductInduced
      (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
      (Shahidi.pairFamily π₁' π₂')
    ∀ h : t + 1 = b + 1,
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (b + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (b + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (b + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (b + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient b F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient b F.Carrier) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier b)],
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)],
    ∀ (μtail : Measure (LeftUnipotentQuotient b F.Carrier))
      (μfull : Measure (LeftUnipotentQuotient t F.Carrier)),
      IsCompatible (upperUnipotent (b + 1) F.Carrier)
        (generalLinearHaar F.Carrier b) (unipotentHaar F.Carrier b) μtail →
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μfull →
      let σtail : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) W :=
        (show t = b by omega) ▸ σ
      zetaSpan (equalRankZetaValues F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μtail π₂ σtail) ≤
      zetaSpan (unequalRankZetaValuesAt 0 (a + 1 + b - t - 1)
        (r := a + 1 + b) (n := t) (by omega)
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μfull
        (rectangularMeasure ν.val 0 (t + 1)) ξ σ)

/-- The test rank is smaller than the tail rank (`T < B`). Both sides
use the zero-row unequal-rank zeta values. -/
def InducedTailSmallerRankSpanStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (a b t : ℕ)
    {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) π₁) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType b (standardCharacter ψ b) π₂) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ) →
    let π₁' : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)
        (ULift.{uV₂} V₁) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
    let π₂' : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier)
        (ULift.{uV₁} V₂) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
    let ξ := F.canonicalNormalizedProductInduced
      (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
      (Shahidi.pairFamily π₁' π₂')
    ∀ h : t + 1 < b + 1,
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)],
    ∀ (μtail : Measure (LeftUnipotentQuotient t F.Carrier))
      (μfull : Measure (LeftUnipotentQuotient t F.Carrier)),
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μtail →
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μfull →
      zetaSpan (unequalRankZetaValuesAt 0 (b - t - 1)
        (r := b) (n := t) (by omega)
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μtail
        (rectangularMeasure ν.val 0 (t + 1)) π₂ σ) ≤
      zetaSpan (unequalRankZetaValuesAt 0 (a + 1 + b - t - 1)
        (r := a + 1 + b) (n := t) (by omega)
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μfull
        (rectangularMeasure ν.val 0 (t + 1)) ξ σ)

/-- The test rank lies strictly between tail and full rank (`B < T < A+B`).
The tail pair is `(σ, π₂)`, with the same canonical `ψ` on its larger member.
The character reversal in the source calculation is a proof obligation. -/
def InducedTailIntermediateRankSpanStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (a b t : ℕ)
    {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier) V₁)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier) V₂)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType a (standardCharacter ψ a) π₁) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType b (standardCharacter ψ b) π₂) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ) →
    let π₁' : Representation ℂ (Langlands.GeneralLinear (a + 1) F.Carrier)
        (ULift.{uV₂} V₁) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₁
    let π₂' : Representation ℂ (Langlands.GeneralLinear (b + 1) F.Carrier)
        (ULift.{uV₁} V₂) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp π₂
    let ξ := F.canonicalNormalizedProductInduced
      (Shahidi.twoBlocks (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b))
      (Shahidi.pairFamily π₁' π₂')
    ∀ (hBT : b + 1 < t + 1) (hTr : t + 1 < (a + 1) + (b + 1)),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (b + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (b + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (b + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (b + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient b F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient b F.Carrier) := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier b)],
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)],
    ∀ (μtail : Measure (LeftUnipotentQuotient b F.Carrier))
      (μfull : Measure (LeftUnipotentQuotient t F.Carrier)),
      IsCompatible (upperUnipotent (b + 1) F.Carrier)
        (generalLinearHaar F.Carrier b) (unipotentHaar F.Carrier b) μtail →
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μfull →
      zetaSpan (unequalRankZetaValuesAt 0 (t - b - 1)
        (r := t) (n := b) (by omega)
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μtail
        (rectangularMeasure ν.val 0 (b + 1)) σ π₂) ≤
      zetaSpan (unequalRankZetaValuesAt 0 (a + 1 + b - t - 1)
        (r := a + 1 + b) (n := t) (by omega)
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μfull
        (rectangularMeasure ν.val 0 (t + 1)) ξ σ)

/-- The three direct-rank cases of the tail Laurent-span comparison.
This aggregate does not include test ranks at least the full induced rank. -/
def InducedTailSpanStatement : Prop :=
  InducedTailEqualRankSpanStatement.{uF, uV₁, uV₂, uW} ∧
  InducedTailSmallerRankSpanStatement.{uF, uV₁, uV₂, uW} ∧
  InducedTailIntermediateRankSpanStatement.{uF, uV₁, uV₂, uW}

end Langlands.RankinSelberg
