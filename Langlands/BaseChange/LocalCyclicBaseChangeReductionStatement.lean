import Langlands.BaseChange.SigmaLiftUniquenessStatement
import Langlands.BaseChange.SigmaLiftTwistStatement
import Langlands.BaseChange.DiscreteSeriesSigmaLiftStatement
import Langlands.BaseChange.SigmaLiftFibreStatement
import Langlands.BaseChange.CuspidalSigmaLiftStructureStatement
import Langlands.BaseChange.CuspidalSigmaLiftExistenceStatement
import Langlands.BaseChange.CuspidalSigmaLiftConductorStatement
import Langlands.Correspondence.HenniartCyclicBaseChange

/-!
# Local cyclic base change of prime degree from the σ-lift statements

The implication from seven local σ-lift statements for `GL_n` over a cyclic extension of
nonarchimedean local fields of characteristic zero to input (I3),
`Langlands.Henniart.LocalCyclicBaseChangeStatement`: the weak form of local cyclic base change
of prime degree for supercuspidal classes. A statement only; see the paired Markdown.
-/

namespace Langlands.BaseChange

universe uK uV

/-- Local cyclic base change of prime degree for supercuspidal classes (input (I3), weak
form) follows from: uniqueness of σ-lifts and their compatibility with character twists
(Henniart–Lemaire 2011, II.2.9, Remarques (2) and (4)), existence of σ-lifts of essentially
square-integrable representations and their fibres (II.4.6–II.4.8), the structure of the
σ-lift of a supercuspidal representation and its converse (II.4.12), and the conductor
identity (Arthur–Clozel 1989, Chapter 1, Proposition 6.9 (ii)). Every field universe of the
premises is `uK` and every representation-space universe is `uV`, as in the conclusion. -/
def LocalCyclicBaseChangeReductionStatement : Prop :=
  SigmaLiftUniquenessStatement.{uK, uK, uV, uV, uV} →
  SigmaLiftTwistStatement.{uK, uK, uV, uV} →
  DiscreteSeriesSigmaLiftStatement.{uK, uK, uV, uV} →
  SigmaLiftFibreStatement.{uK, uK, uV, uV, uV} →
  CuspidalSigmaLiftStructureStatement.{uK, uK, uV, uV} →
  CuspidalSigmaLiftExistenceStatement.{uK, uK, uV, uV} →
  CuspidalSigmaLiftConductorStatement.{uK, uK, uV, uV} →
  Langlands.Henniart.LocalCyclicBaseChangeStatement.{uK, uV}

end Langlands.BaseChange
