import Langlands.Geometry.Building.FullValidity.ChamberAxioms
import Langlands.Group.TitsApartmentPairTransport

/-! # Two-facet apartment transport on the existing building quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.RelativeWeyl
open Langlands.Group.TitsSystem Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- Translation of an actual facet by an element of `G(F)^0`. -/
def zeroFacetTranslate (g : P.zeroSubgroup)
    (Fc : BuildingFacet P.toValuationBuildingData) :
    BuildingFacet P.toValuationBuildingData :=
  ⟨(g : rationalPoints G) • Fc.val,
    ValuationBuildingData.IsFacet.smul P.toValuationBuildingData Fc.property g⟩

@[simp] theorem zeroFacetTranslate_val (g : P.zeroSubgroup)
    (Fc : BuildingFacet P.toValuationBuildingData) :
    (P.zeroFacetTranslate g Fc).val = (g : rationalPoints G) • Fc.val := rfl

@[simp] theorem zeroFacetTranslate_one (Fc : BuildingFacet P.toValuationBuildingData) :
    P.zeroFacetTranslate 1 Fc = Fc := by
  apply Subtype.ext
  exact one_smul _ _

theorem zeroFacetTranslate_mul (g k : P.zeroSubgroup)
    (Fc : BuildingFacet P.toValuationBuildingData) :
    P.zeroFacetTranslate (g * k) Fc =
      P.zeroFacetTranslate g (P.zeroFacetTranslate k Fc) := by
  apply Subtype.ext
  exact mul_smul (g : rationalPoints G) (k : rationalPoints G) Fc.val

/-- Facet stabilizers in `G(F)^0` are equivariant for actual conjugation. -/
theorem facetZeroStabilizer_zeroFacetTranslate (g : P.zeroSubgroup)
    (Fc : BuildingFacet P.toValuationBuildingData) :
    P.facetZeroStabilizer (P.zeroFacetTranslate g Fc) =
      conjugateSubgroup g (P.facetZeroStabilizer Fc) := by
  change MulAction.stabilizer P.zeroSubgroup (g • Fc.val) =
    (MulAction.stabilizer P.zeroSubgroup Fc.val).map (MulAut.conj g).toMonoidHom
  exact MulAction.stabilizer_smul_eq_stabilizer_map_conj g Fc.val

/-- The set of facet stabilizers belonging to facets contained in a subset. -/
def facetStabilizersIn (Y : Set P.ReducedBuilding) : Set (Subgroup P.zeroSubgroup) :=
  P.facetZeroStabilizer '' {Fc | Fc.val ⊆ Y}

/-- Translation of a subset conjugates all its contained facet stabilizers. -/
theorem facetStabilizersIn_smul (g : P.zeroSubgroup) (Y : Set P.ReducedBuilding) :
    P.facetStabilizersIn ((g : rationalPoints G) • Y) =
      conjugateSubgroup g '' P.facetStabilizersIn Y := by
  ext Q
  constructor
  · rintro ⟨Fc, hFc, rfl⟩
    let Fd := P.zeroFacetTranslate g⁻¹ Fc
    have hFd : Fd.val ⊆ Y := by
      change (g : rationalPoints G)⁻¹ • Fc.val ⊆ Y
      exact (Set.smul_set_subset_iff_subset_inv_smul_set).2 (by simpa using hFc)
    refine ⟨P.facetZeroStabilizer Fd, ⟨Fd, hFd, rfl⟩, ?_⟩
    rw [← P.facetZeroStabilizer_zeroFacetTranslate]
    congr 1
    rw [← P.zeroFacetTranslate_mul, mul_inv_cancel, P.zeroFacetTranslate_one]
  · rintro ⟨_, ⟨Fc, hFc, rfl⟩, rfl⟩
    refine ⟨P.zeroFacetTranslate g Fc, Set.smul_set_mono hFc, ?_⟩
    exact P.facetZeroStabilizer_zeroFacetTranslate g Fc

/-- Each point in an actual apartment belongs to a facet wholly in that apartment. -/
theorem exists_buildingFacet_mem_subset_apartment
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    {x : P.ReducedBuilding} (hx : x ∈ Y) :
    ∃ Fc : BuildingFacet P.toValuationBuildingData, x ∈ Fc.val ∧ Fc.val ⊆ Y := by
  obtain ⟨g, rfl⟩ := hY
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hx
  refine ⟨⟨(fun z => g • P.apartmentMap z) ''
    AffineRootSystem.facet P.affineRoots a,
      ⟨g, _, AffineRootSystem.isFacet_facet _ _, rfl⟩⟩,
    ⟨a, AffineRootSystem.mem_facet_self _ _, rfl⟩, ?_⟩
  rintro _ ⟨b, _, rfl⟩
  exact Set.smul_mem_smul_set ⟨b, rfl⟩

variable {P}

/-- Under the Tits correspondence, the contained-facet stabilizers determine
an apartment as an actual subset of the original quotient. -/
theorem IsBuildingTitsSystem.eq_of_facetStabilizersIn_eq
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (h : P.IsBuildingTitsSystem Ca π Sgen)
    {Y Z : Set P.ReducedBuilding} (hY : P.IsApartment Y) (hZ : P.IsApartment Z)
    (heq : P.facetStabilizersIn Y = P.facetStabilizersIn Z) : Y = Z := by
  have hinj : Function.Injective P.facetZeroStabilizer :=
    fun _ _ he => h.bijOn_facetZeroStabilizer.injOn (Set.mem_univ _) (Set.mem_univ _) he
  suffices H : ∀ {Y Z : Set P.ReducedBuilding}, P.IsApartment Y →
      P.facetStabilizersIn Y ⊆ P.facetStabilizersIn Z → Y ⊆ Z from
    Set.Subset.antisymm (H hY heq.subset) (H hZ heq.symm.subset)
  intro Y Z hY hsub x hx
  obtain ⟨Fc, hxFc, hFc⟩ := P.exists_buildingFacet_mem_subset_apartment hY hx
  obtain ⟨Fd, hFd, he⟩ := hsub ⟨Fc, hFc, rfl⟩
  exact hFd ((hinj he) ▸ hxFc)

/-- Every actual apartment has a restricted-apartment representative in the
given Tits system. No distinguished-base identification is assumed. -/
theorem IsBuildingTitsSystem.exists_restrictedApartment_eq
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (h : P.IsBuildingTitsSystem Ca π Sgen)
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y) :
    ∃ a : P.zeroSubgroup,
      restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a =
        P.facetStabilizersIn Y := by
  apply Set.mem_range.mp
  change P.facetStabilizersIn Y ∈
    restrictedApartments (P.chamberZeroStabilizerIn Ca) π Sgen
  rw [← h.apartmentFacetStabilizers_eq]
  obtain ⟨g, rfl⟩ := hY
  exact ⟨g, rfl⟩

/-- The Tits-system comparison gives an actual apartment transporter stabilizing
both common facets setwise, in the original quotient and action. -/
theorem IsBuildingTitsSystem.exists_twoFacet_smul_apartment_eq
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (h : P.IsBuildingTitsSystem Ca π Sgen)
    {Y Z : Set P.ReducedBuilding} (hY : P.IsApartment Y) (hZ : P.IsApartment Z)
    (Fc Fd : BuildingFacet P.toValuationBuildingData)
    (hFcY : Fc.val ⊆ Y) (hFdY : Fd.val ⊆ Y)
    (hFcZ : Fc.val ⊆ Z) (hFdZ : Fd.val ⊆ Z) :
    ∃ k : P.zeroSubgroup,
      k ∈ P.facetZeroStabilizer Fc ∧ k ∈ P.facetZeroStabilizer Fd ∧
        (k : rationalPoints G) • Y = Z := by
  obtain ⟨a, ha⟩ := h.exists_restrictedApartment_eq hY
  obtain ⟨g, hg⟩ := h.exists_restrictedApartment_eq hZ
  obtain ⟨k, hkFc, hkFd, hkA⟩ :=
    h.isTitsSystem.exists_mem_intersection_restrictedApartment_transport a g
      (P := P.facetZeroStabilizer Fc) (Q := P.facetZeroStabilizer Fd)
      (by rw [ha]; exact ⟨Fc, hFcY, rfl⟩)
      (by rw [ha]; exact ⟨Fd, hFdY, rfl⟩)
      (by rw [hg]; exact ⟨Fc, hFcZ, rfl⟩)
      (by rw [hg]; exact ⟨Fd, hFdZ, rfl⟩)
  refine ⟨k, hkFc, hkFd, h.eq_of_facetStabilizersIn_eq
    (ValuationBuildingData.IsApartment.smul _ hY k) hZ ?_⟩
  rw [P.facetStabilizersIn_smul, ← ha, hkA, hg]

variable (P)

/-- A chosen transporter between two apartments, stabilizing each common facet. -/
def twoFacetApartmentTransport
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (h : P.IsBuildingTitsSystem Ca π Sgen)
    {Y Z : Set P.ReducedBuilding} (hY : P.IsApartment Y) (hZ : P.IsApartment Z)
    (Fc Fd : BuildingFacet P.toValuationBuildingData)
    (hFcY : Fc.val ⊆ Y) (hFdY : Fd.val ⊆ Y)
    (hFcZ : Fc.val ⊆ Z) (hFdZ : Fd.val ⊆ Z) :
    ↥(P.facetZeroStabilizer Fc ⊓ P.facetZeroStabilizer Fd) :=
  ⟨(h.exists_twoFacet_smul_apartment_eq hY hZ Fc Fd hFcY hFdY hFcZ hFdZ).choose,
    (h.exists_twoFacet_smul_apartment_eq hY hZ Fc Fd hFcY hFdY hFcZ hFdZ).choose_spec.1,
    (h.exists_twoFacet_smul_apartment_eq hY hZ Fc Fd hFcY hFdY hFcZ hFdZ).choose_spec.2.1⟩

theorem twoFacetApartmentTransport_smul
    {Ca : Set P.Apartment} {W : Type u} [Group W]
    {π : P.normalizerInZero →* W} {Sgen : Set W}
    (h : P.IsBuildingTitsSystem Ca π Sgen)
    {Y Z : Set P.ReducedBuilding} (hY : P.IsApartment Y) (hZ : P.IsApartment Z)
    (Fc Fd : BuildingFacet P.toValuationBuildingData)
    (hFcY : Fc.val ⊆ Y) (hFdY : Fd.val ⊆ Y)
    (hFcZ : Fc.val ⊆ Z) (hFdZ : Fd.val ⊆ Z) :
    (((P.twoFacetApartmentTransport h hY hZ Fc Fd hFcY hFdY hFcZ hFdZ :
      P.zeroSubgroup) : rationalPoints G)) • Y = Z :=
  (h.exists_twoFacet_smul_apartment_eq hY hZ Fc Fd hFcY hFdY hFcZ hFdZ).choose_spec.2.2

end Langlands.Geometry.Building.ParahoricBuildingData
