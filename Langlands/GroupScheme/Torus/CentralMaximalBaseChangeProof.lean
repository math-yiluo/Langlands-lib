import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Torus.CentralMaximalQuotientProof
import Langlands.GroupScheme.Torus.NoTorusBaseChangeReduction
import Langlands.GroupScheme.Torus.NoTorusUnipotent

/-! # Central maximal tori under arbitrary field extension -/

universe u

namespace Langlands.GroupScheme

/-- Central maximal tori under arbitrary field extension, with all structural inputs discharged. -/
theorem centralMaximalTorusBaseChange : CentralMaximalTorusBaseChangeStatement.{u} :=
  centralMaximalTorusBaseChangeReduction.{u} normalSubgroupQuotient.{u}
    centralMaximalTorusQuotientStatement.{u}
    (noTorusBaseChangeReduction.{u} noTorusUnipotent.{u})

end Langlands.GroupScheme
