import Langlands.Representation.RankinSelberg.PairFactorCharacterChangeAssembly
import Langlands.Representation.RankinSelberg.PairFactorEpsilonTransport
import Langlands.Representation.RankinSelberg.CharacterChangeMeasure
import Langlands.Representation.RankinSelberg.RectangularCharacterChangeMeasureProof
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroContinuedFormsProof

/-!
# The unequal-rank pair-factor character change

Over a p-adic field with its canonical topological data, the generic
fixed-functional transport `UnequalRankEpsilonEquation.characterChange` applies
with the published measure laws: the character-change law of compatible quotient
measures, their right invariance, and the right-scaling and character-change laws
of the rectangular product measures. This proves
`FixedFunctionalEpsilonTransportStatement`, and with it
`PairFactorCharacterChangeStatement`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

attribute [local instance] pfccTopology pfccValuativeRel pfccLocalField pfccMeasurable
  pfccBorel pfccGroupMeasurable pfccGroupBorel pfccUnipotentMeasurable pfccUnipotentBorel
  pfccQuotientMeasurable

local instance pfccQuotientBorel {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) :=
  ⟨rfl⟩
local instance pfccSecondCountable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) :
    SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance pfccSigmaCompact {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) :
    SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance pfccMatrixBorel {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (t m : ℕ) :
    BorelSpace (Matrix (Fin t) (Fin m) F.Carrier) :=
  inferInstanceAs (BorelSpace (Fin t → Fin m → F.Carrier))

/-- Theorem: the fixed-functional transport of the unequal-rank epsilon equation
over every p-adic field, for unequal ranks, central characters `ω_π`, `ω_σ` and
Haar measures `ν' = κ ν` with `κ² = |a|`. -/
theorem fixedFunctionalEpsilonTransport :
    FixedFunctionalEpsilonTransportStatement.{uF, uV, uW} := by
  intro p _ F r n hnr V _ _ W _ _ π σ ωπ ωσ hπ hσ ψ ν ν' a κ hκ hκ2 _ μ hμ ℓ ℓ' c m h
  let T := F.canonicalTopologicalData
  have hq : 0 < T.residueCardinality := lt_trans Nat.zero_lt_one T.residueCardinality_gt_one
  have ho : normalizedAbsoluteValue T (a : F.Carrier) =
      (T.residueCardinality : ℝ) ^ (-T.ord (a : F.Carrier)) :=
    T.normalizedAbs_of_ne_zero a.ne_zero
  have hρg : ∀ (t : ℕ) (g : Langlands.GeneralLinear (n + 1) F.Carrier)
      (G : Matrix (Fin t) (Fin (n + 1)) F.Carrier → ℂ),
      ∫ x, G (x * g.val) ∂(rectangularMeasure ν t (n + 1)) =
        determinantWeight (normalizedAbsoluteValue T) g (-(t : ℂ)) *
          ∫ x, G x ∂(rectangularMeasure ν t (n + 1)) :=
    fun t => (padic_rectangular_laws T n t ν).1
  let c' : ℂˣ := Units.mk0 ((c : ℂ) * ((ωπ a : ℂˣ) : ℂ) ^ (n + 1) *
      ((ωσ a : ℂˣ) : ℂ) ^ (r + 1) *
        ((T.normalizedAbs (a : F.Carrier) : ℝ) : ℂ) ^ (-(((r + 1) * (n + 1) : ℕ) : ℂ) / 2))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero c.ne_zero (pow_ne_zero _ (ωπ a).ne_zero))
      (pow_ne_zero _ (ωσ a).ne_zero)) (normalizedAbs_cpow_ne_zero F a _))
  refine ⟨c', Units.val_mk0 _, ?_⟩
  exact UnequalRankEpsilonEquation.characterChange hnr T.residueCardinality hq ψ
    (normalizedAbsoluteValue T) a (T.ord (a : F.Carrier)) ho μ
    (characterChangeCompatibleMeasure p F T n a μ hμ) hμ.right_invariant ν ν' κ hκ hκ2
    (fun t => characterChangeRectangularProductStatement p F T t n ν a) hρg
    π σ ωπ ωσ hπ hσ h c' (Units.val_mk0 _)

/-- Theorem: the change of additive character for unequal-rank pair factors with
self-dual measures, `PairFactorCharacterChangeStatement`. -/
theorem pairFactorCharacterChange : PairFactorCharacterChangeStatement.{uF, uV, uW} :=
  pairFactorCharacterChange_of_transport fixedFunctionalEpsilonTransport
    fixedFunctionalEpsilonTransport

end Langlands.RankinSelberg
