import Langlands.Geometry.Building.KPMoyPrasadFiltrationStatement
import Langlands.Geometry.Building.MoyPrasadProductCoordinates

/-! # Proof: the Moy–Prasad filtration is separated (KP Proposition 13.2.5) -/

universe u

namespace Langlands.Geometry.Building

/-- For supplied parahoric building data satisfying the apartment axioms and a supplied
centralizer filtration satisfying the filtration axioms, `⋂_r P_{x,r} = {1}` at every apartment
point `x` (KP Proposition 13.2.5, opening sentence). -/
theorem moyPrasadSeparated : MoyPrasadSeparatedStatement.{u} := by
  intro F _ _ _ _ G _ P Zf hP hZ x
  exact Zf.iInf_moyPrasad_eq_bot hP hZ.1 x

end Langlands.Geometry.Building
