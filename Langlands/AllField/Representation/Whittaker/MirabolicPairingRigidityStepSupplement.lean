import Langlands.Representation.Whittaker.MirabolicPairingRigidityStep
import Langlands.AllField.Representation.Whittaker.MirabolicPairingRigidityElementary
import Langlands.AllField.Representation.Whittaker.MirabolicPairingRigidityStep
/-!
# The induction step of mirabolic twisted pairing rigidity

The radical-generated case of `MirabolicTwistedPairingRigidityStatement` in rank
`m + 2` is reduced to rank `m + 1` through the unnormalized Bernstein–Zelevinsky
functor `Φ⁻` of the Library. The reduction uses two statements about `Φ⁻`
(`PhiMinusIrreducibleStatement` and `PhiMinusPairingTransferStatement`) and the
functional multiplicity statement in ranks `m + 1` and `m + 2`.
-/

noncomputable section

namespace Langlands.AllField.Whittaker.MirabolicRigidity
open Langlands.Whittaker.MirabolicRigidity hiding RadicalGeneratedPairingRigidity mirabolicTwistedPairingRigidity_of_phiMinus mirabolicTwistedPairingRigidity_of_radicalGenerated nonempty_equiv_of_phiMinus radicalGeneratedPairingRigidity_succ
open Langlands.AllField.Whittaker.MirabolicRigidity
open Langlands.Whittaker hiding MirabolicCompactTwistedPairingStatement MirabolicFunctionalMultiplicityStatement MirabolicTwistedPairingRigidityStatement
open Langlands.AllField.Whittaker

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isEqualRankLPolynomial_characterChange_normalized normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF uV uW

/-! ### Elementary lemmas -/

section Elementary


end Elementary

/-! ### Transfer of Whittaker functionals through `Φ⁻` -/

section Transfer

open Langlands.GeneralLinear.Mirabolic



end Transfer

section PadicTransfer

open Langlands.GeneralLinear.Mirabolic


end PadicTransfer

/-! ### Recognition through `Φ⁻` -/

section Recognition


end Recognition

/-! ### The induction step -/

/-- The radical-generated case in rank `m + 2` follows from rigidity in rank
`m + 1`, the two `Φ⁻` statements and functional multiplicity in ranks `m + 1`
and `m + 2`. -/
theorem radicalGeneratedPairingRigidity_succ 
    (F : Type uF) [Field F] (T : LocalFieldData F) (m : ℕ)
    (hS : MirabolicTwistedPairingRigidityStatement.{uF, uV, uW} F T m)
    (hI : Langlands.AllField.Derivative.Mirabolic.PhiMinusIrreducibleStatement.{uF, uV} F T m)
    (hI' : Langlands.AllField.Derivative.Mirabolic.PhiMinusIrreducibleStatement.{uF, uW} F T m)
    (hP : Langlands.AllField.Derivative.Mirabolic.PhiMinusPairingTransferStatement.{uF, uV, uW} F T m)
    (hM : MirabolicFunctionalMultiplicityStatement.{uF, uV} F T m)
    (hM' : MirabolicFunctionalMultiplicityStatement.{uF, uW} F T m)
    (hN : MirabolicFunctionalMultiplicityStatement.{uF, uV} F T (m + 1))
    (hN' : MirabolicFunctionalMultiplicityStatement.{uF, uW} F T (m + 1)) :
    RadicalGeneratedPairingRigidity.{uF, uV, uW} F T (m + 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ W _ _ ξ ξ' hs hirr hs' hirr' hg _
  let X := (Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ hs)
  let Y := (Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ' hs')
  have hq : 0 < T.residueCardinality :=
    lt_trans Nat.zero_lt_one T.residueCardinality_gt_one
  by_cases hX : (⊥ : Subrepresentation X.representation) = ⊤
  · refine ⟨∅, fun s _ β hβ => ?_⟩
    obtain ⟨β', hβ'⟩ := hP ψ V W ξ ξ' hs hs' hg s β hβ
    exact absurd (forms_eq_zero_of_bot_eq_top_left hX β') hβ'
  by_cases hY : (⊥ : Subrepresentation Y.representation) = ⊤
  · refine ⟨∅, fun s _ β hβ => ?_⟩
    obtain ⟨β', hβ'⟩ := hP ψ V W ξ ξ' hs hs' hg s β hβ
    exact absurd (forms_eq_zero_of_bot_eq_top_right hY β') hβ'
  have hXi : X.representation.IsIrreducible :=
    isIrreducible_of_dichotomy (hI ψ V ξ hs hirr) hX
  have hYi : Y.representation.IsIrreducible :=
    isIrreducible_of_dichotomy (hI' ψ W ξ' hs' hirr') hY
  obtain ⟨E, hE⟩ := hS ψ X Y X.representation Y.representation X.isSmooth hXi Y.isSmooth hYi
  refine ⟨E.image (fun z => z / (T.residueCardinality : ℂ)), fun s hsE β hβ => ?_⟩
  have hsE' : spectralPoint T.residueCardinality (s - 1) ∉ E := by
    intro h
    apply hsE
    refine Finset.mem_image.mpr ⟨_, h, ?_⟩
    have hq' : (T.residueCardinality : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
    rw [spectralPoint_sub_one hq, mul_div_cancel_left₀ _ hq']
  obtain ⟨β', hβ'⟩ := hP ψ V W ξ ξ' hs hs' hg s β hβ
  obtain ⟨eX, eY⟩ := hE (s - 1) hsE' β' hβ'
  exact ⟨nonempty_equiv_of_phiMinus T m hM hN ψ V ξ hs hirr hXi eX,
    nonempty_equiv_of_phiMinus T m hM' hN' ψ W ξ' hs' hirr' hYi eY⟩

/-- Rigidity in every rank follows from the two `Φ⁻` statements and functional
multiplicity in every rank. -/
theorem mirabolicTwistedPairingRigidity_of_phiMinus 
    (F : Type uF) [Field F] (T : LocalFieldData F)
    (hI : ∀ m, Langlands.AllField.Derivative.Mirabolic.PhiMinusIrreducibleStatement.{uF, uV} F T m)
    (hI' : ∀ m, Langlands.AllField.Derivative.Mirabolic.PhiMinusIrreducibleStatement.{uF, uW} F T m)
    (hP : ∀ m, Langlands.AllField.Derivative.Mirabolic.PhiMinusPairingTransferStatement.{uF, uV, uW} F T m)
    (hM : ∀ n, MirabolicFunctionalMultiplicityStatement.{uF, uV} F T n)
    (hM' : ∀ n, MirabolicFunctionalMultiplicityStatement.{uF, uW} F T n) (n : ℕ) :
    MirabolicTwistedPairingRigidityStatement.{uF, uV, uW} F T n := by
  induction n with
  | zero =>
    apply mirabolicTwistedPairingRigidity_of_radicalGenerated
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    intro ψ V _ _ W _ _ ξ ξ' _ hirr _ hirr' _ _
    exact ⟨∅, fun _ _ _ _ => ⟨rankOne_equiv ψ ξ hirr, rankOne_equiv ψ ξ' hirr'⟩⟩
  | succ m ih =>
    exact mirabolicTwistedPairingRigidity_of_radicalGenerated F T (m + 1)
      (radicalGeneratedPairingRigidity_succ F T m ih (hI m) (hI' m) (hP m) (hM m) (hM' m)
        (hM (m + 1)) (hM' (m + 1)))

end Langlands.AllField.Whittaker.MirabolicRigidity
