import Langlands.Geometry.Building.GenericApartmentInjection
import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction

/-! # The maximal-unramified specialization of generic apartment injection -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- Proof of `MaximalUnramifiedApartmentInjectiveStatement`: the general injectivity of the
apartment map applies to the apartment data of every building datum over `K`. -/
theorem maximalUnramifiedApartmentInjective :
    MaximalUnramifiedApartmentInjectiveStatement.{u} := by
  intro F _ _ _ _ H _ C
  exact C.apartment.apartmentMap_injective C.isConnectedReductive C.isMaximalSplitTorus

end Langlands.Geometry.Building
