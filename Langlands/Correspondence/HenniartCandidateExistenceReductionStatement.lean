import Langlands.Correspondence.HenniartStableMapStatement
import Langlands.Global.Factors.RelativeCertifiedPoleComparisonsStatement
import Langlands.Global.Arithmetic.HenniartGlobalizationStatement
import Langlands.ClassFieldTheory.Local.ClassFormationStatement

/-!
# Henniart's candidate existence from its global inputs

Henniart (2000), Théorème 3.1 with 3.7–3.8: the existence of a candidate at every
finite quotient of the absolute Galois group of a p-adic field, stated as a
consequence of the remaining open global and local inputs of the H3 program.
Proposition definition only.
-/

namespace Langlands.Henniart

universe uK uW uP uE uQ

/-- Harris (1998), Proposition 4.8; Henniart (2000), Théorème 2.4; the local
relative class formation with its fundamental classes; the certified local pole
comparisons of Henniart's Lemme 2.8; and the transport of Henniart's 3.8 to the
composite map together imply that every finite quotient `q` of the absolute
Galois group of every p-adic field `K` has a candidate, with automorphic lattice
universe `0`. -/
def CandidateExistenceReductionStatement : Prop :=
  Global.Harris.Proposition48Statement.{uK, 0, 0, 0, uP} →
  ClassField.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionStatement.{0, uW, uP, uP} →
  ClassFieldTheory.Local.LocalRelativeClassFormationStatement.{0} →
  Global.PoleComparison.RelativeCertifiedPoleComparisonsStatement.{0, uW, uP} →
  Global.PoleComparison.HenniartCompositeMapStatement.{0, uK, uW, uP, uE} →
  CandidateExistenceStatement.{uK, uW, 0, uE, uQ}

end Langlands.Henniart
