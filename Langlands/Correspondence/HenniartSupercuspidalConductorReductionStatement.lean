import Langlands.Correspondence.HenniartStableMapStatement
import Langlands.Correspondence.HenniartNumericalStatement
import Langlands.Correspondence.SupercuspidalSpecification
import Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentStatement

/-!
# Henniart's route with the conductor theorem only for supercuspidal p-adic representations

The published `SupercuspidalCorrespondenceHenniartThreeInputsStatement` takes as its third
hypothesis `Conductor.ConductorExponentStatement`, JPSS 1981, Theorem (5.1), for every
generic representation over every nonarchimedean local field. The statement here replaces
that hypothesis by `Conductor.SupercuspidalPadicConductorExponentStatement`, the same
theorem for supercuspidal representations over p-adic fields. The other two hypotheses and
the conclusion are unchanged.
-/

namespace Langlands.Henniart.Extension

open Langlands.Correspondence

universe uK uW uV

/-- Henniart's route to the all-field supercuspidal correspondence from candidate
existence, the surjectivity assertion of Henniart's numerical theorem, and the conductor
exponent of supercuspidal representations over p-adic fields (JPSS 1981, Theorem (5.1),
for supercuspidal representations). -/
def SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement : Prop :=
  CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
  NumericalSurjectivityStatement.{uK, uW, uV} →
  Conductor.SupercuspidalPadicConductorExponentStatement.{uK, uV} →
  SupercuspidalCorrespondenceStatement.{uK, uW, uV}

end Langlands.Henniart.Extension
