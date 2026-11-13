import Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement
import Langlands.Geometry.Building.MoyPrasadDoubleRootConjugation

/-! # Proof: double-root Moy–Prasad covariance (KP Proposition 13.2.5(1), (2)) -/

universe u

namespace Langlands.Geometry.Building

/-- For supplied parahoric building data satisfying the apartment axioms and a supplied
centralizer filtration satisfying the filtration axioms and the double-root commutator bound,
any two Moy–Prasad subgroups presented at the same point of the reduced building and the same
depth are equal (KP Proposition 13.2.5(1) and (2) for supplied data). -/
theorem moyPrasadDoubleRootCovariance : MoyPrasadDoubleRootCovarianceStatement.{u} := by
  intro F _ _ _ _ G _ P Zf hP hZ hZ2 y r Q Q' hQ hQ'
  exact Zf.isMoyPrasadAt_unique_of_doubleRootCommutatorFriendly hP hZ hZ2 y r Q Q' hQ hQ'

end Langlands.Geometry.Building
