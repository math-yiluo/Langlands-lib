import Langlands.Representation.RankinSelberg.CanonicalCharacterChange
import Langlands.Representation.RankinSelberg.PairLFactor

/-!
# Canonical pair L-factors and additive-character scaling
-/

noncomputable section

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open MeasureTheory Polynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{uF} p} (T : K.TopologicalData)

/-- The pair L-factor for the supplied p-adic data and actual measures, conditional on
existence of its common normalized L-polynomial. -/
def canonicalPairLFactor (n r : ℕ) :
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
  (ν : AdditiveHaarMeasure K.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) W)
    (_h : PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) ν π σ),
      RationalFunctionsˣ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  intro ψ ν V _ _ W _ _ π σ h
  exact pairLFactor h

/-- The canonical factor is the reciprocal of any certified pair L-polynomial. -/
theorem canonicalPairLFactor_eq (n r : ℕ) :
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
  (ν : AdditiveHaarMeasure K.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) W)
    (h : PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) ν π σ)
    (P : ℂ[X]) (_hP : IsPairLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) ν π σ P),
      (canonicalPairLFactor T n r ψ ν π σ h : RationalFunctions) =
        (algebraMap ℂ[X] RationalFunctions P)⁻¹ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  intro ψ ν V _ _ W _ _ π σ h P hP
  exact pairLFactor_eq h hP

/-- Character scaling preserves the common normalized polynomial for every block. -/
theorem isPairLPolynomial_characterChange_canonical (n r : ℕ) :
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
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
  (ν : AdditiveHaarMeasure K.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) W) (P : ℂ[X]),
      IsPairLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) ν π σ P ↔
      IsPairLPolynomial T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) ν π σ P := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  intro ψ a ν V _ _ W _ _ π σ P
  by_cases hnr : n < r
  · rw [isPairLPolynomial_of_lt hnr, isPairLPolynomial_of_lt hnr]
    refine forall_congr' fun j => forall_congr' fun k => forall_congr' fun hr => ?_
    subst hr
    exact isUnequalRankLPolynomial_characterChange_canonical T n j k ψ a ν V W π σ P
  · by_cases hrn : r = n
    · subst r
      rw [isPairLPolynomial_self, isPairLPolynomial_self]
      exact isEqualRankLPolynomial_characterChange_canonical T n ψ a V W π σ P
    · exact iff_of_false (not_isPairLPolynomial_of_lt (by omega))
        (not_isPairLPolynomial_of_lt (by omega))

/-- Existence of the common polynomial transfers in both directions under character scaling. -/
theorem pairLPolynomialExists_characterChange_canonical (n r : ℕ) :
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
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
  (ν : AdditiveHaarMeasure K.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) W),
      PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) ν π σ ↔
      PairLPolynomialExists T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) ν π σ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  intro ψ a ν V _ _ W _ _ π σ
  exact exists_congr fun P =>
    isPairLPolynomial_characterChange_canonical T n r ψ a ν π σ P

/-- The selected polynomial is unchanged by character scaling, for any existence witnesses. -/
theorem pairLPolynomial_characterChange_canonical (n r : ℕ) :
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
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
  (ν : AdditiveHaarMeasure K.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) W)
    (h : PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) ν π σ)
    (h' : PairLPolynomialExists T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) ν π σ),
      pairLPolynomial h = pairLPolynomial h' := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  intro ψ a ν V _ _ W _ _ π σ h h'
  exact pairLPolynomial_eq h
    ((isPairLPolynomial_characterChange_canonical T n r ψ a ν π σ _).2
      (pairLPolynomial_spec h'))

/-- The canonical rational-function unit is unchanged by character scaling. -/
theorem canonicalPairLFactor_characterChange (n r : ℕ) :
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
    ∀ (ψ : UnitaryAdditiveCharacter K.Carrier) (a : K.Carrierˣ)
  (ν : AdditiveHaarMeasure K.Carrier)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) W)
    (h : PairLPolynomialExists T.residueCardinality ψ (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) ν π σ)
    (h' : PairLPolynomialExists T.residueCardinality (ψ.scale a) (normalizedAbsoluteValue T)
        (unipotentQuotientHaar K.Carrier n) ν π σ),
      canonicalPairLFactor T n r ψ ν π σ h =
        canonicalPairLFactor T n r (ψ.scale a) ν π σ h' := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear (n + 1) K.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) K.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) K.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n K.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n K.Carrier) := ⟨rfl⟩
  let := T.secondCountableTopology
  let := borel K.Carrier
  let : BorelSpace K.Carrier := ⟨rfl⟩
  intro ψ a ν V _ _ W _ _ π σ h h'
  apply Units.ext
  change (pairLFactor h : RationalFunctions) = (pairLFactor h' : RationalFunctions)
  rw [coe_pairLFactor, coe_pairLFactor,
    pairLPolynomial_characterChange_canonical T n r ψ a ν π σ h h']

end Langlands.RankinSelberg
