import Langlands.Geometry.Building.KPMoyPrasadProductStatement
import Langlands.Geometry.Building.MoyPrasadOrderedEmbedding
import Langlands.Geometry.Building.MoyPrasadProductCoordinates

/-! # Proof: the Moy–Prasad product decomposition at positive depth (KP Proposition 13.2.5(3)) -/

universe u

namespace Langlands.Geometry.Building

/-- For supplied parahoric building data satisfying the apartment axioms and a supplied
centralizer filtration satisfying the filtration axioms, at every apartment point `x` and depth
`r > 0`, for every generic cocharacter `ν` and all injective lists enumerating the indivisible
roots of each sign, the ordered product of the negative blocks, `j(Z(F)_r)` and the positive
blocks is injective with range `P_{x,r}` (KP Proposition 13.2.5(3)). -/
theorem moyPrasadProduct : MoyPrasadProductStatement.{u} := by
  intro F _ _ _ _ G _ P Zf hP hZ x r hr ν hν nneg npos aneg apos haneg hrneg hapos hrpos
  exact ⟨Zf.orderedMoyPrasadProduct_injective x r ν aneg apos haneg hrneg hapos hrpos,
    Zf.range_orderedMoyPrasadProduct_eq hP hZ.1 x r hr ν hν aneg apos hrneg hrpos⟩

end Langlands.Geometry.Building
