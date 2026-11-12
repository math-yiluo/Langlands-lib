import Langlands.Correspondence.HenniartExtensionReduction
import Langlands.Correspondence.HenniartUnitaryTwistProof
import Langlands.Correspondence.HenniartArithmeticTwistProof

/-!
# Henniart's route with the standard inputs discharged

The published reduction `SupercuspidalCorrespondenceHenniartReductionStatement`
has two hypotheses introduced for it: every supercuspidal class is an unramified
twist of a unitary class with central character of finite order, and unramified
twists act on arithmetic pair factors by the expected substitution. Both are
proved (modules `HenniartUnitaryTwistProof` and `HenniartArithmeticTwistProof`).
The remaining hypotheses are published Library statements.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap
open LocalFactor LocalFactor.CommonClosure

universe uK uW uV

/-- Henniart's route to the all-field supercuspidal correspondence: local
converse, candidate existence, the rank induction and unramified-twist
independence of the stable map, normalized local reciprocity, local constants for
every normalized family, and the JPSS unramified-twist law for pair epsilon factors
give the correspondence. -/
def SupercuspidalCorrespondenceHenniartReducedStatement : Prop :=
  RankinSelberg.SupercuspidalLocalConverseStatement.{uK, uV, uV} →
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  StableCorrespondenceStatement.{uK, uW, uV, uW} →
  UnramifiedTwistIndependenceStatement.{uK, uW, uV, uW} →
  LocalClassField.CommonClosureReciprocityExistence.{uK} →
  (∀ (p : ℕ) [Fact p.Prime] (K : PadicField.{uK} p) (eC : ReciprocityFamily K),
    NonabelianSystem.Exists.{uK, uW} K eC) →
  RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV} →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

theorem supercuspidalCorrespondenceHenniartReduced :
    SupercuspidalCorrespondenceHenniartReducedStatement.{uK, uW, uV} := by
  intro hconverse hCE hSC hUTI hrec hsys hGLε
  exact supercuspidalCorrespondenceHenniartReduction hconverse hCE hSC hUTI
    supercuspidalUnitaryFiniteOrderTwist hrec hsys hGLε arithmeticPairUnramifiedTwist

end Langlands.Henniart.Extension
