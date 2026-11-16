import Langlands.Correspondence.HenniartCandidateExistenceReductionStatement
import Langlands.Automorphic.AssociatedFactorTCStatement
import Langlands.Global.Factors.PoleComparisonTCStatement

/-!
# Henniart's candidate existence from its global inputs over totally complex fields

`CandidateExistenceReductionStatement` with its second, fourth and fifth hypotheses replaced
by their totally complex forms: Henniart (2000), Théorème 3.1 with 3.7–3.8, the existence of a
candidate at every finite quotient of the absolute Galois group of a p-adic field, as a
consequence of the remaining open inputs of the H3 program, where the global inputs are
needed only over totally complex number fields. Proposition definition only.
-/

namespace Langlands.Henniart

universe uK uW uP uE uQ

/-- Harris (1998), Proposition 4.8; Henniart (2000), Théorème 2.4, over totally complex
fields; the local relative class formation with its fundamental classes; the certified local
pole comparisons of Henniart's Lemme 2.8, over totally complex fields; and the transport of
Henniart's 3.8 to the composite map, over totally complex fields, together imply that every
finite quotient `q` of the absolute Galois group of every p-adic field `K` has a candidate,
with automorphic lattice universe `0`. -/
def CandidateExistenceTCReductionStatement : Prop :=
  Global.Harris.Proposition48Statement.{uK, 0, 0, 0, uP} →
  ClassField.Global.RelativeWeilGroup.AssociatedSupercuspidalInductionTCStatement.{0, uW, uP, uP} →
  ClassFieldTheory.Local.LocalRelativeClassFormationStatement.{0} →
  Global.PoleComparison.RelativeCertifiedPoleComparisonsTCStatement.{0, uW, uP} →
  Global.PoleComparison.HenniartCompositeMapTCStatement.{0, uK, uW, uP, uE} →
  CandidateExistenceStatement.{uK, uW, 0, uE, uQ}

end Langlands.Henniart
