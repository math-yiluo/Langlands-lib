import Langlands.Geometry.Building.UnramifiedVertexFixerStatements
import Langlands.Geometry.Building.IntegerValuationVertexBoundedOvergroups
import Langlands.Geometry.Building.IntegerValuationCommonApartmentsProof
import Langlands.Geometry.Building.UnramifiedCentralizerNormOneBoundednessProof
import Langlands.Geometry.Building.UnramifiedZeroRootFiltrationBoundedProof

/-! # Maximal bounded vertex one-stabilizers over the unramified field -/

noncomputable section

universe u

open AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building.MaximalUnramified

/-- Every actual vertex one-stabilizer over the maximal unramified field is
maximal among the algebraically bounded subgroups of the original group. -/
theorem vertexOneStabilizerMaximalBounded :
    VertexOneStabilizerMaximalBoundedStatement.{u} := by
  intro F _ _ _ _ G _ C y hy
  let := ValuativeRel.ofValuation (fixedFieldValued F).v
  let : (valuation F).Compatible := valuation_compatible F
  exact C.maximal_oneStabilizer_vertex_of_isAlgebraicallyBounded
    (commonApartments F G C) hy
    ((oneStabilizerBounded_of_centralizer_of_zeroRootFiltration
      centralizerNormOneBounded zeroRootFiltrationBounded) F G C y)

end Langlands.Geometry.Building.MaximalUnramified
