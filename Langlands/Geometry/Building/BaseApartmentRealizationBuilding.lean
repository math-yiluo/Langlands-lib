import Langlands.Geometry.Building.AffineTitsRealizationBuilding

/-! # Building assembly from one original apartment -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

namespace ValuationBuildingData.PolysimplicialRealization

variable {B : ValuationBuildingData G} (R : B.PolysimplicialRealization)

/-- Face compatibility transports polysimpliciality of the original apartment
to every actual apartment of the same quotient. -/
theorem isPolysimplicial_apartment_of_base (hR : R.IsFaceCompatible)
    (hbase : AbstractBuilding.IsPolysimplicial
      (R.apartmentComplex B.apartmentImage))
    {Y : Set B.ReducedBuilding} (hY : B.IsApartment Y) :
    AbstractBuilding.IsPolysimplicial (R.apartmentComplex Y) := by
  obtain ⟨g, rfl⟩ := hY
  exact hbase.of_orderIso
    (R.apartmentTranslateOrderIso hR g B.apartmentImage (g • B.apartmentImage) rfl)

/-- The universal apartment premise is equivalent to the original-apartment
premise; the reverse implication needs only face compatibility. -/
theorem isPolysimplicial_all_apartments_iff (hR : R.IsFaceCompatible) :
    (∀ Y, B.IsApartment Y →
      AbstractBuilding.IsPolysimplicial (R.apartmentComplex Y)) ↔
    AbstractBuilding.IsPolysimplicial (R.apartmentComplex B.apartmentImage) :=
  ⟨fun h => h _ B.isApartment_apartmentImage,
    fun h _ hY => R.isPolysimplicial_apartment_of_base hR h hY⟩

end ValuationBuildingData.PolysimplicialRealization

namespace ParahoricBuildingData

variable {P : ParahoricBuildingData G} {Ca : Set P.Apartment}
  {W : Type u} [Group W] {π : P.normalizerInZero →* W} {Sgen : Set W}

/-- The general Tits comparison assembles a building from a single
original-apartment polysimplicial witness. -/
theorem IsBuildingTitsSystem.realization_isBuilding_of_base
    (hT : P.IsBuildingTitsSystem Ca π Sgen)
    (R : P.toValuationBuildingData.PolysimplicialRealization)
    (hR : R.IsFaceCompatible)
    (hadm : ∀ s ∈ Sgen, IsAdmissibleType Sgen {s})
    (hbase : AbstractBuilding.IsPolysimplicial
      (R.apartmentComplex P.apartmentImage)) :
    AbstractBuilding.IsBuilding R.complex R.apartments :=
  hT.realization_isBuilding R hR hadm
    (fun _ hY => R.isPolysimplicial_apartment_of_base hR hbase hY)

variable (P) [P.normalizerZero.Normal]

set_option linter.defProp false in
/-- Construct the building on the actual affine Tits datum, using only the
original-apartment polysimplicial premise. -/
def affineTitsRealizationBuildingOfBase
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots)
    (hA : AffineRootSystem.IsAffineRootSystemWithRankZero P.affineRoots)
    (hCa : AffineRootSystem.IsChamber P.affineRoots Ca)
    (hT : P.IsBuildingTitsSystem Ca P.affineTitsProjection
      (P.chamberSimpleInAffinePart e Ca))
    (R : P.toValuationBuildingData.PolysimplicialRealization)
    (hR : R.IsFaceCompatible)
    (hbase : AbstractBuilding.IsPolysimplicial
      (R.apartmentComplex P.apartmentImage)) :
    AbstractBuilding.IsBuilding R.complex R.apartments :=
  P.affineTitsRealizationBuilding e hA hCa hT R hR
    (fun _ hY => R.isPolysimplicial_apartment_of_base hR hbase hY)

end ParahoricBuildingData
end Langlands.Geometry.Building
