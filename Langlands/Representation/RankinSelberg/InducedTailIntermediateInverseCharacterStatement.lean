import Langlands.Representation.RankinSelberg.CanonicalCharacterChange
import Langlands.Representation.RankinSelberg.PairLFactor

/-! # Actual unequal-rank zeta values at the inverse additive character -/

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear Whittaker HarmonicAnalysis MeasureTheory

universe uF uV uW

/-- Actual unequal-rank rational zeta-value sets agree at a character and its
inverse, for independently supplied quotient measures with the same normalized
Haar inputs. This is an internal prerequisite for the intermediate-tail proof. -/
def InducedTailIntermediateInverseCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uF} p) (T : K.TopologicalData)
    (n r j k : ℕ) (hr : r = n + (j + k + 1)),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) K.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n K.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
    letI := T.secondCountableTopology
    letI := borel K.Carrier
    letI : BorelSpace K.Carrier := ⟨rfl⟩
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier)
      (η : AdditiveHaarMeasure K.Carrier)
      (μ μinv : Measure (LeftUnipotentQuotient n K.Carrier)),
      QuotientIntegration.IsCompatible (upperUnipotent (n + 1) K.Carrier)
        (generalLinearHaar K.Carrier n) (unipotentHaar K.Carrier n) μ →
      QuotientIntegration.IsCompatible (upperUnipotent (n + 1) K.Carrier)
        (generalLinearHaar K.Carrier n) (unipotentHaar K.Carrier n) μinv →
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        {W : Type uW} [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
        (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) W),
        unequalRankZetaValuesAt j k hr T.residueCardinality ψ (normalizedAbsoluteValue T)
          μ (rectangularMeasure η j (n + 1)) π σ =
        unequalRankZetaValuesAt j k hr T.residueCardinality
          (ψ.scale (-1 : K.Carrierˣ)) (normalizedAbsoluteValue T)
          μinv (rectangularMeasure η j (n + 1)) π σ

end Langlands.RankinSelberg
