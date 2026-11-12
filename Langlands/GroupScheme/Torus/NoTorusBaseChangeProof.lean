import Langlands.GroupScheme.Torus.NoTorusBaseChangeReduction
import Langlands.GroupScheme.Torus.NoTorusUnipotent

/-! # Absence of tori under arbitrary field extension -/

universe u

namespace Langlands.GroupScheme

/-- Absence of tori under arbitrary field extension, with all structural inputs discharged. -/
theorem noTorusBaseChange : NoTorusBaseChangeStatement.{u} :=
  noTorusBaseChangeReduction.{u} noTorusUnipotent.{u}

end Langlands.GroupScheme
