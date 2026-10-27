import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Shahidi.Induction
import Mathlib.Algebra.Module.ULift

/-!
# Equal-rank rank-one extension Laurent-span comparison

An internal comparison for the equal-rank rank-one extension divisibility
target: every corank-one zeta value of `π × σ₁` lies in the Laurent span of
the equal-rank zeta values of `π` against the actual upper normalized
induction of `(χ, σ₁)`. It is derived from JPSS (1983), Proposition 9.1,
printed 452–454, and the last-row reduction of printed 449, displays (1)
and (3). This module only defines the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- The equal-rank rank-one extension Laurent-span comparison. For `π` on
`GL_(t+2)` and `σ₁` on `GL_(t+1)`, both of Whittaker type, the Laurent span of
the actual block `j = k = 0` zeta values of `π × σ₁` is contained in the
Laurent span of the actual equal-rank zeta values of `π`, transported along
`t + 1 = 1 + t`, against the published upper normalized induction in the
ordered blocks `(χ, σ₁)`. This holds for all compatible quotient measures on
both sides. Only the rank-one carrier is lifted to the universe of `σ₁`. No
induced Whittaker-type, polynomial-existence or irreducibility premise is
imposed. -/
def EqualRankRankOneExtensionSpanComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    (t : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (t + 2) F.Carrier) V)
    (σ₁ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier),
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (t + 1) (standardCharacter ψ (t + 1)) π) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ₁) →
    let χlift : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier)
        (ULift.{uW} ℂ) :=
      (ULift.moduleEquiv.symm.conjRingEquiv.toMonoidHom).comp
        (rankOneCharacter (χ : F.Carrierˣ →* ℂˣ))
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
    letI := borel (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent ((1 + t) + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent ((1 + t) + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient (1 + t) F.Carrier)
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)],
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (1 + t))],
    ∀ (μbase : Measure (LeftUnipotentQuotient t F.Carrier))
      (μind : Measure (LeftUnipotentQuotient (1 + t) F.Carrier)),
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μbase →
      IsCompatible (upperUnipotent ((1 + t) + 1) F.Carrier)
        (generalLinearHaar F.Carrier (1 + t)) (unipotentHaar F.Carrier (1 + t)) μind →
      ∀ hrn : t + 1 = 1 + t,
        zetaSpan (unequalRankZetaValuesAt (r := t + 1) (n := t) 0 0 rfl
          F.canonicalTopologicalData.residueCardinality ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) μbase
          (rectangularMeasure ν 0 (t + 1)) π σ₁) ≤
        zetaSpan (equalRankZetaValues (n := 1 + t)
          F.canonicalTopologicalData.residueCardinality ψ
          (normalizedAbsoluteValue F.canonicalTopologicalData) μind
          (hrn ▸ π : Representation ℂ (Langlands.GeneralLinear ((1 + t) + 1) F.Carrier) V)
          (F.canonicalNormalizedProductInduced
            (Shahidi.twoBlocks 1 (t + 1) (Nat.succ_pos 0) (Nat.succ_pos t))
            (Shahidi.pairFamily χlift σ₁)))

end Langlands.RankinSelberg
