import Langlands.Representation.RankinSelberg.RankOneExtensionTransport

/-!
# Strict rank-one extension Laurent-span comparison

JPSS (1983), Lemma (5.5), printed 423–427: in the strict rank range, every
block-one zeta value of `π × σ₁` lies in the Laurent span of the block-zero
zeta values of `π` against the actual lower induction `(σ₁, χ)`. This module
only defines the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The early JPSS Lemma (5.5) comparison in its original strict rank range
`t + 3 ≤ r + 1`. The Laurent span of the actual block-one zeta values of
`π × σ₁`, with predecessor rank `t`, is contained in the Laurent span of the
actual block-zero zeta values of `π` against the published lower induction of
`(σ₁, χ)`, with predecessor rank `1 + t`. Both sides have the same trailing
index `r - t - 2`. Only the rank-one carrier is lifted to the universe of `σ₁`.
No induced Whittaker-type, polynomial-existence or irreducibility premise is
imposed. -/
def RankOneExtensionSpanComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
    (hrt : t + 3 ≤ r + 1),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ₁) →
    let χlift : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier)
        (ULift.{uW} ℂ) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
        (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
    let hrBase : r = t + (1 + (r - t - 2) + 1) := by omega
    let hrInd : r = (1 + t) + (0 + (r - t - 2) + 1) := by omega
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
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient (1 + t) F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)],
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (1 + t))],
    ∀ (μbase : Measure (LeftUnipotentQuotient t F.Carrier))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F.Carrier)),
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μbase →
      IsCompatible (upperUnipotent ((1 + t) + 1) F.Carrier)
        (generalLinearHaar F.Carrier (1 + t)) (unipotentHaar F.Carrier (1 + t)) μind →
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := t) 1 (r - t - 2) hrBase
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μbase
        (rectangularMeasure ν.val 1 (t + 1)) π σ₁) ≤
      zetaSpan (unequalRankZetaValuesAt (r := r) (n := 1 + t) 0 (r - t - 2) hrInd
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μind
        (rectangularMeasure ν.val 0 ((1 + t) + 1)) π
        (rankOneExtensionLowerInduced F t χlift σ₁))

end Langlands.RankinSelberg
