import Langlands.Geometry.Building.IntegerFacetVertexFixingStatement
import Langlands.Geometry.Building.ApartmentFacetClosureFixing

/-! # Proof that closed facets are fixed through their vertices -/

noncomputable section

universe u

namespace Langlands.Geometry.Building

/-- Closed apartment facets are fixed through their vertices for integer valuation building
data. Only the affine root system hypothesis is used; the affine Weyl lifting hypothesis of the
statement is not needed. -/
theorem integerFacetVertexFixing : IntegerFacetVertexFixingStatement.{u} :=
  fun _ _ _ _ _ B hΨ _ => B.smul_apartmentMap_eq_of_vertices_fixed hΨ

end Langlands.Geometry.Building
