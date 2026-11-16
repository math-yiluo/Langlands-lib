import Langlands.GroupScheme.RelativeLevi.SplitBorelPositiveChart
import Langlands.GroupScheme.RelativeUnipotent.RootHeightFiltration

/-! # Root-height chart on the actual split Borel contracting group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {R : Type u} [CommRing R] {I J : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- The positive chart is a root-height chart on its actual contracting group. -/
def SplitBorelPositiveChart.toRootHeightChart (c : SplitBorelPositiveChart i P) :
    RelativeUnipotent.RootHeightChart
      (AffineRegularBorel.contractingGroup i c.cocharacter) where
  dimension := c.dimension
  roots := c.roots
  height := c.height
  height_pos := c.height_pos
  chart := c.chart
  formula := c.formula
  commutator := c.commutator

end Langlands.GroupScheme
