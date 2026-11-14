import Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.AllField.Representation.Whittaker.MirabolicPairingStatementSupplement
/-!
# Elementary cases of mirabolic twisted pairing rigidity

For an irreducible representation of the mirabolic group, the radical either
acts trivially or the vectors `ξ u x - x` span the whole space. This module
proves the rank-one case and the cases in which at least one representation has
trivial radical action. Only the case of two radical-generated representations
remains, recorded as `RadicalGeneratedPairingRigidity`.
-/

noncomputable section

namespace Langlands.AllField.Whittaker.MirabolicRigidity
open Langlands.Whittaker.MirabolicRigidity hiding RadicalGeneratedPairingRigidity mirabolicTwistedPairingRigidity_of_radicalGenerated
open Langlands.AllField.Whittaker.MirabolicRigidity
open Langlands.Whittaker hiding MirabolicCompactTwistedPairingStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isEqualRankLPolynomial_characterChange_normalized normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF uV uW

/-! ### The radical dichotomy -/

section Radical


end Radical

/-! ### Rank one -/

section RankOne



end RankOne

/-! ### Two radical-trivial representations -/

section Spectral




end Spectral

/-! ### Reduction of the rigidity statement to the radical-generated case -/

/-- The remaining case of `MirabolicTwistedPairingRigidityStatement`: both
representations are radical-generated. -/
def RadicalGeneratedPairingRigidity 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) : Prop :=
  letI := T.topology
  letI : IsTopologicalRing F := by
    let := T.valuativeRel
    let := T.localField
    infer_instance
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (ξ : Representation ℂ (mirabolic n F) V)
      (ξ' : Representation ℂ (mirabolic n F) W),
      IsSmooth ξ → Representation.IsIrreducible ξ →
      IsSmooth ξ' → Representation.IsIrreducible ξ' →
      IsRadicalGenerated ξ → IsRadicalGenerated ξ' →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        ∀ β : InvariantBilinear.forms ξ ξ'
          (fun g => determinantWeight (normalizedAbsoluteValue T) g.val (-s)),
          β ≠ 0 →
            Nonempty (ξ.Equiv (mirabolicCompactInduced ψ n)) ∧
            Nonempty (ξ'.Equiv (mirabolicCompactInduced ψ n))

/-- Rigidity follows from its radical-generated case. -/
theorem mirabolicTwistedPairingRigidity_of_radicalGenerated 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ)
    (hgen : RadicalGeneratedPairingRigidity.{uF, uV, uW} F T n) :
    MirabolicTwistedPairingRigidityStatement.{uF, uV, uW} F T n := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ W _ _ ξ ξ' hs hirr hs' hirr'
  cases n with
  | zero =>
    exact ⟨∅, fun _ _ _ _ => ⟨rankOne_equiv ψ ξ hirr, rankOne_equiv ψ ξ' hirr'⟩⟩
  | succ m =>
    have : SecondCountableTopology
        (Langlands.GeneralLinear (m + 1 + 1) F) :=
      T.generalLinearSecondCountableTopology (m + 1 + 1)
    have : SecondCountableTopology (mirabolic (m + 1) F) :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    have hχ : ∀ s : ℂ, ∀ u : Mirabolic.radical (m + 1) F,
        (fun g : mirabolic (m + 1) F =>
          determinantWeight (normalizedAbsoluteValue T) g.val (-s)) u = 1 :=
      fun s u => determinantWeight_radical _ u (-s)
    rcases radicalTrivial_or_radicalGenerated ξ hirr with ht | hg <;>
      rcases radicalTrivial_or_radicalGenerated ξ' hirr' with ht' | hg'
    · obtain ⟨E, hE⟩ := exists_finset_of_radicalTrivial (Nat.succ_pos m)
        (normalizedAbsoluteValue T) T.residueCardinality
        (lt_trans Nat.zero_lt_one T.residueCardinality_gt_one)
        (Langlands.LocalFactor.LocalAbelian.uniformizerUnit T)
        (by rw [normalizedAbsoluteValue_apply, Langlands.LocalFactor.LocalAbelian.uniformizerUnit_coe]
            exact T.normalizedAbs_uniformizer)
        hs hirr hs' hirr' ht ht'
      exact ⟨E, fun s hsE β hβ => absurd (hE s hsE β) hβ⟩
    · exact ⟨∅, fun s _ β hβ =>
        absurd (forms_eq_zero_of_trivial_of_generated (hχ s) ht hg' β) hβ⟩
    · exact ⟨∅, fun s _ β hβ =>
        absurd (forms_eq_zero_of_generated_of_trivial (hχ s) hg ht' β) hβ⟩
    · exact hgen ψ V W ξ ξ' hs hirr hs' hirr' hg hg'

end Langlands.AllField.Whittaker.MirabolicRigidity
