import Langlands.Geometry.Building.TitsRealizationGalleries
import Langlands.Geometry.Building.TitsRealizationThickness
import Langlands.Geometry.Building.RealizationApartmentTransport
import Langlands.Geometry.Building.AffineSimpleAdmissibility

/-! # Conditional building construction for the actual affine Tits datum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {P : ParahoricBuildingData G} {Ca : Set P.Apartment} {W : Type u} [Group W]
  {π : P.normalizerInZero →* W} {Sgen : Set W}

namespace IsBuildingTitsSystem

variable (hT : P.IsBuildingTitsSystem Ca π Sgen)
  (R : P.toValuationBuildingData.PolysimplicialRealization)
  (hR : R.IsFaceCompatible)
  (hadm : ∀ s ∈ Sgen, IsAdmissibleType Sgen {s})

include hT hR hadm

/-- BL1 follows from actual chamber connectivity and the global panel count. -/
theorem realization_isThick : AbstractBuilding.IsThick R.complex.facets :=
  ⟨hT.realization_isChamberComplex R hR hadm,
    hT.realization_three_le_encard_chambersContaining R hR⟩

/-- BL2 retains the explicit polysimplicial structure of the apartment. -/
theorem realization_isThin_apartment
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    (hpoly : AbstractBuilding.IsPolysimplicial (R.apartmentComplex Y)) :
    AbstractBuilding.IsThin (R.apartmentComplex Y) :=
  ⟨hT.realization_isChamberComplex_apartment R hR hadm hY hpoly,
    hT.realization_encard_apartment_chambersContaining_eq_two R hR hY⟩

/-- All four building clauses on the original realization, with the remaining
apartment polysimplicial premise explicit. -/
theorem realization_isBuilding
    (hpoly : ∀ Y, P.IsApartment Y →
      AbstractBuilding.IsPolysimplicial (R.apartmentComplex Y)) :
    AbstractBuilding.IsBuilding R.complex R.apartments where
  thick := hT.realization_isThick R hR hadm
  isSubcomplex := by
    rintro _ ⟨Y, hY, rfl⟩
    exact hT.realization_isSubcomplex_apartmentComplex R hR hY
  thin := by
    rintro _ ⟨Y, hY, rfl⟩
    exact hT.realization_isThin_apartment R hR hadm hY (hpoly Y hY)
  exists_apartment := hT.realization_exists_apartment R
  exists_orderIso := hT.realization_exists_orderIso R hR

end IsBuildingTitsSystem

variable (P) [P.normalizerZero.Normal]

/-- A multiplicative affine-Weyl comparison transfers an actual noncommuting
chamber-simple neighbor to the literal affine part. -/
theorem exists_noncommuting_chamberSimpleInAffinePart
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots)
    (hA : AffineRootSystem.IsAffineRootSystemWithRankZero P.affineRoots)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {s : P.affinePart} (hs : s ∈ P.chamberSimpleInAffinePart e C) :
    ∃ t ∈ P.chamberSimpleInAffinePart e C, s * t ≠ t * s := by
  have hes : e s ∈ AffineRootSystem.chamberSimpleReflections P.affineRoots C := hs
  obtain ⟨t, ht, hst⟩ := hA.exists_noncommuting_chamberSimpleReflection hC hes
  refine ⟨e.symm t, ?_, ?_⟩
  · change e (e.symm t) ∈ AffineRootSystem.chamberSimpleReflections P.affineRoots C
    simpa only [e.apply_symm_apply] using ht
  · intro hcomm
    apply hst
    simpa only [map_mul, e.apply_symm_apply] using congrArg e hcomm

/-- Every singleton simple type of the actual affine Tits datum is admissible. -/
theorem isAdmissibleType_singleton_chamberSimpleInAffinePart
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots)
    (hA : AffineRootSystem.IsAffineRootSystemWithRankZero P.affineRoots)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {s : P.affinePart} (hs : s ∈ P.chamberSimpleInAffinePart e C) :
    IsAdmissibleType (P.chamberSimpleInAffinePart e C) {s} := by
  refine ⟨Set.singleton_subset_iff.mpr hs, ?_⟩
  intro r hr
  by_cases hrs : r = s
  · subst r
    obtain ⟨t, ht, hst⟩ :=
      P.exists_noncommuting_chamberSimpleInAffinePart e hA hC hs
    refine ⟨t, ht, Relation.ReflTransGen.single ⟨hs, ht, hst⟩, ?_⟩
    intro hts
    rw [Set.mem_singleton_iff] at hts
    exact hst (by rw [hts])
  · exact ⟨r, hr, Relation.ReflTransGen.refl,
      fun h => hrs (Set.mem_singleton_iff.mp h)⟩

set_option linter.defProp false in
/-- A building witness for the literal affine Tits datum, on the supplied
realization of the original quotient. The affine-root and chamber hypotheses
discharge singleton admissibility; apartment polysimpliciality remains supplied. -/
def affineTitsRealizationBuilding
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots)
    (hA : AffineRootSystem.IsAffineRootSystemWithRankZero P.affineRoots)
    (hCa : AffineRootSystem.IsChamber P.affineRoots Ca)
    (hT : P.IsBuildingTitsSystem Ca P.affineTitsProjection
      (P.chamberSimpleInAffinePart e Ca))
    (R : P.toValuationBuildingData.PolysimplicialRealization)
    (hR : R.IsFaceCompatible)
    (hpoly : ∀ Y, P.IsApartment Y →
      AbstractBuilding.IsPolysimplicial (R.apartmentComplex Y)) :
    AbstractBuilding.IsBuilding R.complex R.apartments :=
  hT.realization_isBuilding R hR
    (fun _ hs => P.isAdmissibleType_singleton_chamberSimpleInAffinePart e hA hCa hs)
    hpoly

end Langlands.Geometry.Building.ParahoricBuildingData
