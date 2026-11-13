import Langlands.Representation.Conductor.TrivialCharacterEpsilonStatement
import Langlands.Representation.Conductor.RankOneTateReduction
import Langlands.Representation.GodementJacquet.LocalTateConductorProof
import Langlands.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationStatement
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.RankinSelberg.WhittakerTypeFromMultiplicityProof
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.Representation.Whittaker.LocalFieldMultiplicityOneProof

/-!
# Reduction of the trivial-character epsilon factor to the all-field functional equation

`TrivialCharacterEpsilonStatement` follows from the separately stated
`LocalFieldUnequalRankFunctionalEquationStatement` at carrier universes `uV` and `0`.
The case `n = 0` uses the published local Tate theorem and needs no premise.
`TrivialCharacterEpsilonProof` discharges the premise with its published proof.
-/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.Whittaker Langlands.HarmonicAnalysis
open Langlands.RankinSelberg MeasureTheory QuotientIntegration
open Langlands.GeneralLinear.Iwasawa

universe uF uV

/-- The trivial character of `GL_1` is smooth: the whole group fixes every vector. -/
theorem rankOneCharacter_one_isSmooth {F : Type uF} [Field F] [TopologicalSpace F] :
    IsSmooth (rankOneCharacter (F := F) 1) := by
  intro v
  refine ⟨⊤, ?_⟩
  intro g
  simp [characterRepresentation, twist]

/-- The trivial character of `GL_1` is of Whittaker type for the inverse standard
character. -/
theorem rankOneCharacter_one_isOfWhittakerType_inverse {F : Type uF} [Field F]
    [TopologicalSpace F] [IsTopologicalRing F] (ψ : UnitaryAdditiveCharacter F) :
    IsOfWhittakerType 0 (inverseStandardCharacter ψ 0) (rankOneCharacter (F := F) 1) :=
  (isOfWhittakerType_standard_iff_inverse ψ _).mp
    (scalar_isOfWhittakerType_rankOne ψ _ rankOneCharacter_one_isSmooth)

/-- Over every nonarchimedean local field, an irreducible admissible generic
representation of `GL_(r+1)(F)` is of Whittaker type for the standard character:
the published all-field multiplicity-one theorem supplies the scalar condition. -/
theorem isOfWhittakerType_of_isGeneric_localField {F : Type uF} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V] {ψ : UnitaryAdditiveCharacter F}
    {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
    (hπ : IsGeneric ψ r π) :
    IsOfWhittakerType r (standardCharacter ψ r) π := by
  obtain ⟨ℓ, hℓ⟩ := hπ.2.2
  exact whittakerTypeFromMultiplicity F r (standardCharacter ψ r) V π hπ.1 hπ.2.1
    ⟨ℓ, hℓ, fun ℓ' => (localFieldMultiplicityOne F r V ψ π hπ.2.1 hπ.1 ℓ ℓ' hℓ).exists⟩

/-- `TrivialCharacterEpsilonStatement` from the all-field unequal-rank functional
equation. For `n = 0` the published local Tate theorem gives the equal-rank relation;
for `n = m + 1` the functional equation at the constructed quotient measure and one
nonzero functional pair transports to every compatible measure and every pair. -/
theorem trivialCharacterEpsilon_of_localFieldUnequalRankFunctionalEquation
    (h : RankinSelberg.LocalFieldUnequalRankFunctionalEquationStatement.{uF, uV, 0}) :
    TrivialCharacterEpsilonStatement.{uF, uV} := by
  intro F _ _ _ _ _ _ _ _ _ _ _ _ _ _ q hq abv ϖ hϖ habvϖ habvunit ψ hψ ν hν n V _ _ π hπ
  cases n with
  | zero =>
    obtain ⟨c, a, h1, -⟩ := conductorExponent_rankOne_of_localTate F q hq abv ϖ hϖ habvϖ
      habvunit ψ hψ ν hν GodementJacquet.localTateConductor π hπ
    exact ⟨(c, (a : ℤ)), h1⟩
  | succ m =>
    have hnr : 0 < m + 1 := Nat.succ_pos m
    have hπW := isOfWhittakerType_of_isGeneric_localField hπ
    have hσW := rankOneCharacter_one_isOfWhittakerType_inverse (F := F) ψ
    obtain ⟨ℓ, hℓ⟩ := hπW.exists_ne_zero
    obtain ⟨ℓ', hℓ'⟩ := hσW.exists_ne_zero
    have hconc := h F 0 (m + 1) q hq abv ϖ hϖ habvϖ habvunit hnr ψ
      (unipotentQuotientHaar F 0) (unipotentQuotientHaar_isCompatible F 0) ν hν V ℂ π
      (rankOneCharacter 1) hπW hσW ℓ ℓ' hℓ hℓ'
    obtain ⟨c, k, hEq⟩ := exists_unequalRankEpsilonEquation_iff.mpr hconc
    exact ⟨(c, k), (isPairEpsilonFactor_of_lt hnr).mpr
      (unequalRankEpsilonFactor_of_equation hnr hπW hσW hℓ hℓ' hEq)⟩

end Langlands.Conductor
