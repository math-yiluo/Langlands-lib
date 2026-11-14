import Langlands.Geometry.Building.UnramifiedVertexFixerStatements
import Langlands.Geometry.Building.IntegerValuationAffineWeylProof
import Langlands.Geometry.Building.MaximalUnramifiedUniformizer
import Langlands.Geometry.Building.IntegerVertexFixerApproximation
import Langlands.Geometry.Building.ApartmentFacetClosureFixing

/-! # Finite vertex fixer approximation over the actual maximal unramified field -/

noncomputable section

universe u

namespace Langlands.Geometry.Building.MaximalUnramified

/-- The exact finite vertex approximation statement, with all geometric inputs discharged. -/
theorem finiteVertexFixerApproximation :
    FiniteVertexFixerApproximationStatement.{u} := by
  intro F _ _ _ _ G _ C g Ωa hne hΩ
  have hΨ := C.isAffineRootSystemWithRankZero_affineRoots (exists_order_eq_one F)
  exact C.finiteVertexFixerApproximation_of_closedFacetsFixedByVertices hΨ
    (C.smul_apartmentMap_eq_of_vertices_fixed hΨ) g Ωa hne hΩ

end Langlands.Geometry.Building.MaximalUnramified
