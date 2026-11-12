import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardReduction
import Langlands.GroupScheme.Torus.CentralizerSmoothProof
import Langlands.GroupScheme.Torus.CentralMaximalBaseChangeReduction
import Langlands.GroupScheme.NormalSubgroupQuotientProof
import Langlands.GroupScheme.Torus.CentralMaximalQuotientProof
import Langlands.GroupScheme.Torus.NoTorusBaseChangeReduction
import Langlands.GroupScheme.Torus.NoTorusUnipotent

/-! # Maximal tori remain maximal after field extension -/

universe u

namespace Langlands.GroupScheme

/-- Maximal tori remain maximal after field extension, with all structural inputs discharged. -/
theorem maximalTorusBaseChangeForward : MaximalTorusBaseChangeForwardStatement.{u} :=
  maximalTorusBaseChangeForwardReduction.{u} torusCentralizerSmooth.{u}
    (centralMaximalTorusBaseChangeReduction.{u} normalSubgroupQuotient.{u}
      centralMaximalTorusQuotientStatement.{u}
      (noTorusBaseChangeReduction.{u} noTorusUnipotent.{u}))

end Langlands.GroupScheme
