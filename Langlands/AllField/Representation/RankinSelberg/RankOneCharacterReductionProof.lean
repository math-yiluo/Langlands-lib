import Langlands.Representation.RankinSelberg.RankOneCharacterReductionProof
import Langlands.AllField.Representation.RankinSelberg.RankOneCharacterReductionStatement
/-!
# Proof of the reduction of full rank-one Whittaker type to a quasicharacter

The algebraic dual of the carrier is the whole rank-one functional space, hence
linearly equivalent to `ℂ`. A functional corresponding to `1` is then a linear
equivalence of the carrier with `ℂ`, and transporting the action gives a
character. A smooth vector supplies an open kernel, hence continuity.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement RankOneCharacterReductionStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply rankOneCharacterReduction
open Langlands.AllField.RankinSelberg

open _root_.Topology
open Langlands.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.GeneralLinear

universe uF uV uG

section Algebra



end Algebra

section RankOne



end RankOne

/-- The arbitrary-carrier reduction of full rank-one Whittaker type to the
scalar representation of a continuous quasicharacter. -/
theorem rankOneCharacterReduction : RankOneCharacterReductionStatement.{uF, uV} := by
  intro F _ _ _ _ ψ V _ _ π hπ
  have := (⟨⟩ : LocalFieldData F).generalLinearTopologicalGroup 1
  exact exists_quasicharacter_equiv_of_isOfWhittakerType ψ π hπ

end Langlands.AllField.RankinSelberg
