import Langlands.GroupScheme.Reductive.NormalSubgroupReductiveStatement
import Langlands.GroupScheme.Reductive.NormalSubgroup

/-! # Reductivity of smooth connected normal subgroups -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected closed normal subgroup of a connected reductive group
over a field is connected reductive. -/
theorem normalSubgroupReductive : NormalSubgroupReductiveStatement.{u} := by
  intro k _ G hG N n hClosed hSmooth hConnected hNormal
  let : Smooth N.X.hom := hSmooth
  let : ConnectedSpace N.X.left := hConnected
  exact hG.of_normalSubgroup n hClosed hNormal

end Langlands.GroupScheme
