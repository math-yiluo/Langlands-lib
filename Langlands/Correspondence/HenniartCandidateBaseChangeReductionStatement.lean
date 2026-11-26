import Langlands.Correspondence.HenniartCandidateBaseChangeCompatibility
import Langlands.Correspondence.HenniartNumericalDescentStatement
import Langlands.Correspondence.SupercuspidalSpecification

/-!
# Henniart's route with the candidate compatible with cyclic base change

The final form of Option II of the operator's numerical LLC route note (§7.1,
last paragraph) with source (b) for input (I4): candidate existence, the
compatibility of the candidate with cyclic base change of prime degree, the
GL-side upper bound (I1), the Laumon–Deligne count (LD), the twist Swan bound and
the existence of Artin conductors imply the supercuspidal correspondence.
A proposition only.
-/

namespace Langlands.Henniart

universe uK uW uV

open Langlands.Correspondence

/-- Candidate existence with the compatibility of the candidate with cyclic base
change of prime degree, (I1), (LD), the supercuspidal twist Swan bound and the
existence of Artin conductors imply the supercuspidal correspondence over every
p-adic field. -/
def SupercuspidalCorrespondenceHenniartCandidateBaseChangeStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  CandidateBaseChangeCompatibilityStatement.{uK, uW, uV} →
  SupercuspidalStratumUpperBoundStatement.{uK, uV} →
  LaumonDeligneCountStatement.{uK, uW} →
  SupercuspidalTwistSwanBoundStatement.{uK, uV} →
  WeilArtinConductorExistenceStatement.{uK, uW} →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

end Langlands.Henniart
