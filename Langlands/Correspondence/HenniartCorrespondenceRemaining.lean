import Langlands.Correspondence.HenniartCorrespondenceReduction
import Langlands.Correspondence.HenniartTwistIndependenceProof
import Langlands.Representation.RankinSelberg.SupercuspidalLocalConverseProof
import Langlands.Representation.RankinSelberg.UnramifiedTwistEpsilonProof

/-!
# Henniart's route with local converse, twist independence and the unramified-twist law proved

The published `SupercuspidalCorrespondenceHenniartReducedStatement` has seven
hypotheses. Three of them are now proved: `RankinSelberg.SupercuspidalLocalConverseStatement`
by the published `RankinSelberg.supercuspidalLocalConverse`,
`UnramifiedTwistIndependenceStatement` from candidate existence and local
reciprocity by `unramifiedTwistIndependence_of_reciprocity`, and
`RankinSelberg.UnramifiedTwistEpsilonStatement` by `RankinSelberg.unramifiedTwistEpsilon`.
The four that remain are published Library statements.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap
open LocalFactor LocalFactor.CommonClosure

universe uK uW uV

/-- Henniart's route to the all-field supercuspidal correspondence: candidate
existence, the rank induction of the stable map, normalized local reciprocity,
and local constants for every normalized family give the correspondence. -/
def SupercuspidalCorrespondenceHenniartRemainingStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  StableCorrespondenceStatement.{uK, uW, uV, uW} →
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
    NonabelianSystem.Exists.{uK, uW} K eC) →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

theorem supercuspidalCorrespondenceHenniartRemaining :
    SupercuspidalCorrespondenceHenniartRemainingStatement.{uK, uW, uV} := by
  intro hCE hSC hrec hsys
  exact supercuspidalCorrespondenceHenniartReduced
    RankinSelberg.supercuspidalLocalConverse hCE hSC
    (unramifiedTwistIndependence_of_reciprocity hCE hrec) hrec hsys
    RankinSelberg.unramifiedTwistEpsilon

end Langlands.Henniart.Extension
