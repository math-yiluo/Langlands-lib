import Langlands.Geometry.Building.KPMoyPrasadDoubleRootStatement
import Langlands.Geometry.Building.MoyPrasadCommutatorGenerators

/-! # Proof: `[P_{x,r}, P_{x,s}] ⊆ P_{x,r+s}` with the double-root premise (KP Proposition 13.2.5(4)) -/

universe u

namespace Langlands.Geometry.Building

/-- For supplied parahoric building data satisfying the apartment axioms and a supplied
centralizer filtration satisfying the filtration axioms and double-root commutator
friendliness, `⁅P_{x,r}, P_{x,s}⁆ ≤ P_{x,r+s}` at every apartment point `x` and all
`r, s ≥ 0` (KP Proposition 13.2.5(4) for supplied data). -/
theorem moyPrasadDoubleRootCommutator : MoyPrasadDoubleRootCommutatorStatement.{u} := by
  intro F _ _ _ _ G _ P Zf hP hZ hZ2 x r s
  exact Zf.commutator_moyPrasad_le hP hZ hZ2 x r s

end Langlands.Geometry.Building
