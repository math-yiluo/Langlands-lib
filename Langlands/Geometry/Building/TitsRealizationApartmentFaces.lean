import Langlands.Group.TitsApartmentFaces
import Langlands.Geometry.Building.TitsRealizationChambers
import Langlands.Geometry.Building.TitsFacetApartmentTransport

/-! # Faces and chambers inside actual apartments from the Tits comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem Langlands.Group.RelativeWeyl
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} {Ca : Set P.Apartment} {W : Type u} [Group W]
  {π : P.normalizerInZero →* W} {Sgen : Set W}

namespace IsBuildingTitsSystem

variable (hT : P.IsBuildingTitsSystem Ca π Sgen)
include hT

/-- Every original subface of a facet in an actual apartment is in that apartment. -/
theorem subset_apartment_of_facetPrecedes
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    {Fc Fd : BuildingFacet P.toValuationBuildingData}
    (hface : FacetPrecedes P.toValuationBuildingData Fc Fd) (hFdY : Fd.val ⊆ Y) :
    Fc.val ⊆ Y := by
  obtain ⟨a, ha⟩ := hT.exists_restrictedApartment_eq hY
  have hFd : P.facetZeroStabilizer Fd ∈
      restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a := by
    rw [ha]
    exact ⟨Fd, hFdY, rfl⟩
  have hFc := hT.isTitsSystem.mem_restrictedApartment_of_le hFd
    (hT.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ Fc))
    ((hT.facetPrecedes_iff Fc Fd).mp hface)
  rw [ha] at hFc
  obtain ⟨Fe, hFe, heq⟩ := hFc
  have hsame : Fe = Fc := hT.bijOn_facetZeroStabilizer.injOn
    (Set.mem_univ _) (Set.mem_univ _) heq
  exact hsame ▸ hFe

variable (R : P.toValuationBuildingData.PolysimplicialRealization)
  (hR : R.IsFaceCompatible)
include hR

/-- The full Tits comparison makes every realized apartment a subcomplex. -/
theorem realization_isSubcomplex_apartmentComplex
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y) :
    AbstractBuilding.IsSubcomplex (R.apartmentComplex Y) R.complex.facets := by
  refine ⟨fun _ h => h.choose, ?_⟩
  rintro A ⟨hA, hAY⟩ C hC hCA
  exact ⟨hC, hT.subset_apartment_of_facetPrecedes hY
    ((hR ⟨C, hC⟩ ⟨A, hA⟩).mp hCA) hAY⟩

/-- A facet in an actual apartment lies in a global chamber of that apartment. -/
theorem realization_exists_apartment_chamber_with_stabilizer
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    (Fc : R.complex.facets) (hFcY : (R.realize Fc).val ⊆ Y) :
    ∃ (Cd : R.complex.facets) (g : P.zeroSubgroup),
      AbstractBuilding.IsChamber R.complex.facets Cd.val ∧ Fc.val ⊆ Cd.val ∧
        (R.realize Cd).val ⊆ Y ∧
          P.facetZeroStabilizer (R.realize Cd) =
            conjugateSubgroup g (P.chamberZeroStabilizerIn Ca) := by
  obtain ⟨a, ha⟩ := hT.exists_restrictedApartment_eq hY
  have hFc : P.facetZeroStabilizer (R.realize Fc) ∈
      restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a := by
    rw [ha]
    exact ⟨R.realize Fc, hFcY, rfl⟩
  obtain ⟨n, hn, hle⟩ :=
    hT.isTitsSystem.exists_conjugate_borel_le_in_restrictedApartment hFc
  rw [ha] at hn
  obtain ⟨Fd, hFdY, hFd⟩ := hn
  let Cd := R.realize.symm Fd
  have hCd : P.facetZeroStabilizer (R.realize Cd) =
      conjugateSubgroup (a * n) (P.chamberZeroStabilizerIn Ca) := by
    simpa only [Cd, Equiv.apply_symm_apply] using hFd
  refine ⟨Cd, a * n,
    hT.realization_isChamber_of_stabilizer_eq_conjugate_borel R hR Cd (a * n) hCd,
    ?_, ?_, hCd⟩
  · apply (hR Fc Cd).mpr
    apply (hT.facetPrecedes_iff _ _).mpr
    rw [hCd]
    exact hle
  · change Fd.val ⊆ Y at hFdY
    simpa only [Cd, Equiv.apply_symm_apply] using hFdY

/-- The chamber-extension clause holds within every realized apartment. -/
theorem realization_exists_apartment_chamber
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y) :
    ∀ A ∈ R.apartmentComplex Y, ∃ C,
      AbstractBuilding.IsChamber R.complex.facets C ∧
        C ∈ R.apartmentComplex Y ∧ A ⊆ C := by
  rintro A ⟨hA, hAY⟩
  obtain ⟨Cd, _, hCd, hsub, hCdY, _⟩ :=
    hT.realization_exists_apartment_chamber_with_stabilizer R hR hY ⟨A, hA⟩ hAY
  exact ⟨Cd.val, hCd, ⟨Cd.property, hCdY⟩, hsub⟩

/-- A chosen global chamber in the same actual apartment, containing the facet. -/
def realizationContainingApartmentChamber
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    (Fc : R.complex.facets) (hFcY : (R.realize Fc).val ⊆ Y) : R.complex.facets :=
  (hT.realization_exists_apartment_chamber_with_stabilizer R hR hY Fc hFcY).choose

theorem realizationContainingApartmentChamber_spec
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    (Fc : R.complex.facets) (hFcY : (R.realize Fc).val ⊆ Y) :
    AbstractBuilding.IsChamber R.complex.facets
        (hT.realizationContainingApartmentChamber R hR hY Fc hFcY).val ∧
      Fc.val ⊆ (hT.realizationContainingApartmentChamber R hR hY Fc hFcY).val ∧
        (R.realize (hT.realizationContainingApartmentChamber R hR hY Fc hFcY)).val ⊆ Y := by
  obtain ⟨_, hCd, hsub, hCdY, _⟩ :=
    (hT.realization_exists_apartment_chamber_with_stabilizer R hR hY Fc hFcY).choose_spec
  exact ⟨hCd, hsub, hCdY⟩

/-- The maximal facets of an apartment are exactly its global chambers. -/
theorem realization_isChamber_apartmentComplex_iff
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    (C : Set (∀ i, R.V i)) :
    AbstractBuilding.IsChamber (R.apartmentComplex Y) C ↔
      AbstractBuilding.IsChamber R.complex.facets C ∧ C ∈ R.apartmentComplex Y := by
  constructor
  · intro hC
    obtain ⟨D, hD, hDY, hCD⟩ :=
      hT.realization_exists_apartment_chamber R hR hY C hC.1
    have heq : C = D := Set.Subset.antisymm hCD (hC.2 hDY hCD)
    exact ⟨heq ▸ hD, hC.1⟩
  · rintro ⟨hC, hCY⟩
    refine ⟨hCY, ?_⟩
    intro D hDY hCD
    exact hC.2 ((hT.realization_isSubcomplex_apartmentComplex R hR hY).1 hDY) hCD

end IsBuildingTitsSystem
end Langlands.Geometry.Building.ParahoricBuildingData
