import Langlands.Geometry.Building.RootFreeBuildingGeometry
import Langlands.Geometry.Building.FullValidity.ChamberAxioms

/-! # The actual Tits witness for an anisotropic building -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem

namespace Langlands.Group.TitsSystem

variable {A : Type u} [Group A] {N : Subgroup A} {W : Type v} [Group W]

/-- With full Borel subgroup, the empty standard parabolic remains the full group
under every conjugation. -/
theorem conjStandardParabolic_top_empty (π : N →* W) (g : A) :
    conjStandardParabolic ⊤ π g ∅ = (⊤ : Subgroup A) := by
  rw [conjStandardParabolic, standardParabolic_empty (B := ⊤) (π := π) le_top]
  change ((⊤ : Subgroup A).map (MulAut.conj g).toMonoidHom : Set A) = _
  rw [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective]

/-- For empty simple reflections and full Borel subgroup, the sole admissible
parabolic is the full group. -/
theorem isAdmissibleParabolic_top_empty_iff (π : N →* W) (Q : Subgroup A) :
    IsAdmissibleParabolic ⊤ π ∅ Q ↔ Q = ⊤ := by
  constructor
  · intro hQ
    obtain ⟨g, hg⟩ := hQ.isParabolic
    rw [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at hg
    exact top_unique hg
  · rintro rfl
    exact ⟨1, ∅, ⟨subset_rfl, fun _ hs => hs.elim⟩,
      (conjStandardParabolic_top_empty π 1).symm⟩

/-- Every apartment of this rank-zero restricted building has its sole parabolic. -/
theorem restrictedApartment_top_empty (π : N →* W) (g : A) :
    restrictedApartment ⊤ π ∅ g = {⊤} := by
  ext Q
  constructor
  · intro hQ
    exact Set.mem_singleton_iff.2
      ((isAdmissibleParabolic_top_empty_iff π Q).1
        (isAdmissibleParabolic_of_mem_restrictedApartment hQ))
  · rintro rfl
    exact ⟨1, ∅, ⟨subset_rfl, fun _ hs => hs.elim⟩,
      (conjStandardParabolic_top_empty π (g * 1)).symm⟩

theorem restrictedApartments_top_empty (π : N →* W) :
    restrictedApartments ⊤ π ∅ = {{⊤}} := by
  simp [restrictedApartments, restrictedApartment_top_empty]

/-- The full group is a saturated BN pair with trivial Weyl group and no
simple reflections. -/
theorem isTitsSystem_top_trivial (N : Subgroup A) :
    IsTitsSystem (⊤ : Subgroup A) N (1 : N →* PUnit.{v + 1}) ∅ where
  surjective _ := ⟨1, Subsingleton.elim _ _⟩
  ker_eq := by ext n; simp
  sup_eq := by simp
  closure_eq := Subsingleton.elim _ _
  ne_one _ hs := hs.elim
  mul_self _ hs := hs.elim
  mul_mem_cell _ hs := hs.elim
  conj_not_le _ hs := hs.elim

theorem isSaturated_top : IsSaturated (⊤ : Subgroup A) ⊤ := by
  simp [IsSaturated]

end Langlands.Group.TitsSystem

namespace Langlands.Geometry.Building

open BruhatTits.IntegralModels

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The facets of the actual reduced quotient are inhabited. -/
theorem nonempty_buildingFacet : Nonempty (BuildingFacet B) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty B.Apartment)
  exact ⟨⟨B.apartmentMap '' AffineRootSystem.facet B.affineRoots x,
    B.isFacet_image ⟨x, rfl⟩⟩⟩

/-- A one-point actual quotient has one facet, with its original facet predicate. -/
theorem subsingleton_buildingFacet (hB : Subsingleton B.ReducedBuilding) :
    Subsingleton (BuildingFacet B) := by
  have := hB
  exact ⟨fun Fc Fc' => Subtype.ext
    ((Fc.property.nonempty.eq_univ).trans (Fc'.property.nonempty.eq_univ).symm)⟩

/-- The canonical apartment fills a one-point actual quotient. -/
theorem apartmentImage_eq_univ_of_subsingleton (hB : Subsingleton B.ReducedBuilding) :
    B.apartmentImage = Set.univ := by
  have := hB
  obtain ⟨x⟩ := (inferInstance : Nonempty B.Apartment)
  exact (show B.apartmentImage.Nonempty from ⟨B.apartmentMap x, x, rfl⟩).eq_univ

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The stabilizer in `G(F)^0` of the whole actual quotient is the full group. -/
theorem zeroStabilizerIn_univ : P.zeroStabilizerIn Set.univ = ⊤ := by
  ext g
  simp [mem_zeroStabilizerIn, Set.smul_set_univ]

/-- On a one-point quotient every actual building facet has full stabilizer. -/
theorem facetZeroStabilizer_eq_top_of_subsingleton
    (hB : Subsingleton P.ReducedBuilding) (Fc : BuildingFacet P.toValuationBuildingData) :
    P.facetZeroStabilizer Fc = ⊤ := by
  have := hB
  rw [facetZeroStabilizer, Fc.property.nonempty.eq_univ, P.zeroStabilizerIn_univ]

/-- A chamber's actual image has full stabilizer on a one-point quotient. -/
theorem chamberZeroStabilizerIn_eq_top_of_subsingleton
    (hB : Subsingleton P.ReducedBuilding) {Ca : Set P.Apartment}
    (hCa : AffineRootSystem.IsChamber P.affineRoots Ca) :
    P.chamberZeroStabilizerIn Ca = ⊤ := by
  have := hB
  obtain ⟨x, -, rfl⟩ := hCa
  have hY : (P.apartmentMap '' AffineRootSystem.facet P.affineRoots x).Nonempty :=
    ⟨_, x, AffineRootSystem.mem_facet_self _ _, rfl⟩
  rw [chamberZeroStabilizerIn, hY.eq_univ, P.zeroStabilizerIn_univ]

/-- The actual facet-stabilizer apartments of a one-point quotient are the singleton
collection consisting of the full stabilizer. -/
theorem apartmentFacetStabilizers_eq_of_subsingleton
    (hB : Subsingleton P.ReducedBuilding) :
    P.apartmentFacetStabilizers = {{⊤}} := by
  have hA := P.toValuationBuildingData.apartmentImage_eq_univ_of_subsingleton hB
  have hQ : ∀ h : rationalPoints G,
      P.facetZeroStabilizer '' {Fc | Fc.val ⊆ h • P.apartmentImage} = {⊤} := by
    intro h
    rw [hA, Set.smul_set_univ]
    ext Q
    constructor
    · rintro ⟨Fc, -, rfl⟩
      exact Set.mem_singleton_iff.2
        (P.facetZeroStabilizer_eq_top_of_subsingleton hB Fc)
    · rintro rfl
      obtain ⟨Fc⟩ := P.toValuationBuildingData.nonempty_buildingFacet
      exact ⟨Fc, Set.subset_univ _, P.facetZeroStabilizer_eq_top_of_subsingleton hB Fc⟩
  ext Q
  change (∃ h : rationalPoints G,
    Q = P.facetZeroStabilizer '' {Fc | Fc.val ⊆ h • P.apartmentImage}) ↔ Q ∈ {{⊤}}
  simp only [hQ, Set.mem_singleton_iff, exists_const]

/-- The explicit trivial Weyl datum satisfies all six existing building-system fields
on an actual one-point quotient with full normalizer. -/
theorem isBuildingTitsSystem_trivial_of_subsingleton_of_normalizer_eq_top
    (hB : Subsingleton P.ReducedBuilding) (hN : normalizerPoints P.i = ⊤)
    {Ca : Set P.Apartment} (hCa : AffineRootSystem.IsChamber P.affineRoots Ca) :
    P.IsBuildingTitsSystem Ca (1 : P.normalizerInZero →* PUnit.{u + 1}) ∅ := by
  have hNZ : P.normalizerInZero = ⊤ := by
    simp [normalizerInZero, hN]
  have hFc := P.toValuationBuildingData.subsingleton_buildingFacet hB
  have hI := P.chamberZeroStabilizerIn_eq_top_of_subsingleton hB hCa
  let π : P.normalizerInZero →* PUnit.{u + 1} := 1
  refine ⟨?_, Set.finite_empty, ?_, ?_, ?_, ?_⟩
  · rw [hI]
    exact isTitsSystem_top_trivial _
  · rw [hI, hNZ]
    exact isSaturated_top
  · refine ⟨?_, ?_, ?_⟩
    · intro Fc _
      rw [Set.mem_ofPred_eq, hI, isAdmissibleParabolic_top_empty_iff]
      exact P.facetZeroStabilizer_eq_top_of_subsingleton hB Fc
    · intro Fc _ Fc' _ _
      exact hFc.elim Fc Fc'
    · intro Q hQ
      rw [Set.mem_ofPred_eq, hI, isAdmissibleParabolic_top_empty_iff] at hQ
      obtain ⟨Fc⟩ := P.toValuationBuildingData.nonempty_buildingFacet
      exact ⟨Fc, Set.mem_univ _,
        (P.facetZeroStabilizer_eq_top_of_subsingleton hB Fc).trans hQ.symm⟩
  · intro Fc Fc'
    rw [P.facetZeroStabilizer_eq_top_of_subsingleton hB Fc,
      P.facetZeroStabilizer_eq_top_of_subsingleton hB Fc']
    constructor
    · intro _
      exact le_refl _
    · intro _
      rw [hFc.elim Fc Fc']
      exact facetPrecedes_refl _ _
  · rw [hI, P.apartmentFacetStabilizers_eq_of_subsingleton hB,
      restrictedApartments_top_empty]

/-- The complete existing KP Tits predicate follows on the actual one-point quotient
when the actual normalizer is the whole rational-point group. -/
theorem hasTitsSystem_of_subsingleton_of_normalizer_eq_top
    (hB : Subsingleton P.ReducedBuilding) (hN : normalizerPoints P.i = ⊤) :
    P.HasTitsSystem := by
  intro Ca hCa
  exact ⟨PUnit.{u + 1}, inferInstance, 1, ∅,
    P.isBuildingTitsSystem_trivial_of_subsingleton_of_normalizer_eq_top hB hN hCa⟩

/-- The actual trivial Weyl map with all six building-system fields on each chamber
of supplied anisotropic parahoric data. -/
def anisotropicTitsData (hG : IsAnisotropic G) (Ca : Set P.Apartment)
    (hCa : AffineRootSystem.IsChamber P.affineRoots Ca) :
    {π : P.normalizerInZero →* PUnit.{u + 1} // P.IsBuildingTitsSystem Ca π ∅} :=
  ⟨1, P.isBuildingTitsSystem_trivial_of_subsingleton_of_normalizer_eq_top
    (P.apartment.subsingleton_reducedBuilding_of_isAnisotropic hG
      P.isMaximalSplitTorus.isSplitSubtorus)
    (hG.normalizerPoints_eq_top_of_isSplitSubtorus P.isMaximalSplitTorus.isSplitSubtorus) hCa⟩

@[simp]
theorem anisotropicTitsData_val (hG : IsAnisotropic G) (Ca : Set P.Apartment)
    (hCa : AffineRootSystem.IsChamber P.affineRoots Ca) :
    (P.anisotropicTitsData hG Ca hCa).val = 1 :=
  rfl

/-- KP Axiom 4.1.9 holds for supplied actual parahoric data on an anisotropic group. -/
theorem hasTitsSystem_of_isAnisotropic (hG : IsAnisotropic G) : P.HasTitsSystem :=
  P.hasTitsSystem_of_subsingleton_of_normalizer_eq_top
    (P.apartment.subsingleton_reducedBuilding_of_isAnisotropic hG
      P.isMaximalSplitTorus.isSplitSubtorus)
    (hG.normalizerPoints_eq_top_of_isSplitSubtorus P.isMaximalSplitTorus.isSplitSubtorus)

end ParahoricBuildingData

end Langlands.Geometry.Building
