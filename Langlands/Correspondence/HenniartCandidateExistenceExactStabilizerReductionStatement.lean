import Langlands.Correspondence.HenniartCandidateExistenceReductionStatement
import Langlands.Correspondence.HenniartCandidateExistenceTCReductionStatement
import Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerStatement

/-!
# Henniart's candidate existence from Proposition 4.8 under the exact stabilizer condition

The published `CandidateExistenceReductionStatement` and
`CandidateExistenceTCReductionStatement`, each with its first hypothesis, Harris (1998),
Proposition 4.8, taken in its exact-stabilizer form
`Global.Harris.Proposition48ExactStabilizerStatement` (the auxiliary character subject to
Harris's condition (4.12) in the proof of Lemma 4.7). The other four hypotheses and the
conclusion are unchanged. Each implies its published counterpart (proved below). Neither
statement is proved here.
-/

namespace Langlands.Henniart

universe uK uW uP uE uQ

/-- Harris (1998), Proposition 4.8 in its exact-stabilizer form; Henniart (2000),
Théorème 2.4; the local relative class formation with its fundamental classes; the
certified local pole comparisons of Henniart's Lemme 2.8; and the transport of Henniart's
3.8 to the composite map together imply that every finite quotient `q` of the absolute
Galois group of every p-adic field `K` has a candidate, with automorphic lattice universe
`0`. This is `CandidateExistenceReductionStatement` with
`Global.Harris.Proposition48ExactStabilizerStatement` in place of
`Global.Harris.Proposition48Statement`, at the same universes; nothing else is
changed. -/
def CandidateExistenceExactStabilizerReductionStatement : Prop :=
  Global.Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP} →
  ClassFieldTheory.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP} →
  ClassFieldTheory.Local.LocalRelativeClassFormationStatement.{0} →
  Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement.{0, uW, uP} →
  Global.PoleComparison.HenniartCompositeMapStatement.{0, uK, uW, uP, uE} →
  CandidateExistenceStatement.{uK, uW, 0, uE, uQ}

/-- Harris (1998), Proposition 4.8 in its exact-stabilizer form; Henniart (2000),
Théorème 2.4, over totally complex fields; the local relative class formation with its
fundamental classes; the certified local pole comparisons of Henniart's Lemme 2.8, over
totally complex fields; and the transport of Henniart's 3.8 to the composite map, over
totally complex fields, together imply that every finite quotient `q` of the absolute
Galois group of every p-adic field `K` has a candidate, with automorphic lattice universe
`0`. This is `CandidateExistenceTCReductionStatement` with
`Global.Harris.Proposition48ExactStabilizerStatement` in place of
`Global.Harris.Proposition48Statement`, at the same universes; nothing else is
changed. -/
def CandidateExistenceExactStabilizerTCReductionStatement : Prop :=
  Global.Harris.Proposition48ExactStabilizerStatement.{uK, 0, 0, 0, uP} →
  ClassFieldTheory.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionTCStatement.{0, uW, uP, uP} →
  ClassFieldTheory.Local.LocalRelativeClassFormationStatement.{0} →
  Global.PoleComparison.RelativeCertifiedPoleComparisonsTCStatement.{0, uW, uP} →
  Global.PoleComparison.HenniartCompositeMapTCStatement.{0, uK, uW, uP, uE} →
  CandidateExistenceStatement.{uK, uW, 0, uE, uQ}

/-- The exact-stabilizer candidate reduction implies the published one, because
`Global.Harris.Proposition48Statement` implies
`Global.Harris.Proposition48ExactStabilizerStatement`. -/
theorem candidateExistenceReductionStatement_of_exactStabilizer
    (h : CandidateExistenceExactStabilizerReductionStatement.{uK, uW, uP, uE, uQ}) :
    CandidateExistenceReductionStatement.{uK, uW, uP, uE, uQ} :=
  fun hHarris =>
    h (Global.Harris.proposition48ExactStabilizerStatement_of_proposition48Statement hHarris)

/-- The totally complex exact-stabilizer candidate reduction implies the published one. -/
theorem candidateExistenceTCReductionStatement_of_exactStabilizer
    (h : CandidateExistenceExactStabilizerTCReductionStatement.{uK, uW, uP, uE, uQ}) :
    CandidateExistenceTCReductionStatement.{uK, uW, uP, uE, uQ} :=
  fun hHarris =>
    h (Global.Harris.proposition48ExactStabilizerStatement_of_proposition48Statement hHarris)

end Langlands.Henniart
