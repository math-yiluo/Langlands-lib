import Langlands.Geometry.Building.TitsFacetApartmentTransport
import Langlands.Group.TitsApartmentStabilizer
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductStatement

/-! # The stabilizer of the apartment of `S` under the Tits comparison -/

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
  {P : ParahoricBuildingData G} {Ca : Set P.Apartment} {W : Type u} [Group W]
  {π : P.normalizerInZero →* W} {Sgen : Set W}

/-- The facet of `B(G)` given by a facet `Ca` of `A(S)`. -/
def chamberFacet (hCa : AffineRootSystem.IsFacet P.affineRoots Ca) :
    BuildingFacet P.toValuationBuildingData :=
  ⟨P.apartmentMap '' Ca, P.toValuationBuildingData.isFacet_image hCa⟩

/-- KP Fact 2.6.22 for the minimal Levi subgroup `Z_G(S)` gives
`G(F) = G(F)^0 N(F)`: the factor in `G(F)^♮` lies in `G(F)^0`, and the factor
in `Z(F)` lies in `N(F)`. -/
theorem exists_zero_mul_normalizer
    (hfact : SimplyConnectedCentralizerProductStatement.{u}) (g : rationalPoints G) :
    ∃ k ∈ P.zeroSubgroup, ∃ n ∈ normalizerPoints P.toValuationBuildingData.i, g = k * n := by
  obtain ⟨c, z, hcz⟩ := hfact F P.S G P.centralizer.Z P.zeroDatum.C P.zeroDatum.D P.i
    P.centralizer.j P.zeroDatum.d P.zeroDatum.π P.zeroDatum.isSimplyConnectedDerivedCover
    P.isMaximalSplitTorus P.centralizer.isRepresentedBy g
  exact ⟨_, P.zeroDatum.simplyConnectedImage_le_zeroSubgroup ⟨c, rfl⟩, _,
    centralizerPoints_le_normalizerPoints P.i
      (map_mem_centralizerPoints P.centralizer.isRepresentedBy z), hcz⟩

namespace IsBuildingTitsSystem

variable (hT : P.IsBuildingTitsSystem Ca π Sgen)
  (hCa : AffineRootSystem.IsFacet P.affineRoots Ca)
include hT hCa

/-- The facet stabilizers of the facets contained in `A(S)` form the standard
apartment of the restricted building. -/
theorem facetStabilizersIn_apartmentImage :
    P.facetStabilizersIn P.apartmentImage =
      restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen 1 := by
  have hmem : P.facetStabilizersIn P.apartmentImage ∈ P.apartmentFacetStabilizers :=
    ⟨1, by rw [one_smul]; rfl⟩
  rw [hT.apartmentFacetStabilizers_eq] at hmem
  obtain ⟨a, ha⟩ := hmem
  rw [← ha]
  apply hT.isTitsSystem.restrictedApartment_eq_one_of_forall hT.isSaturated
  intro m
  rw [ha]
  refine ⟨P.zeroFacetTranslate (m : P.zeroSubgroup) (chamberFacet hCa), ?_, ?_⟩
  · rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩
    have hmN : ((m : P.zeroSubgroup) : rationalPoints G) ∈ normalizerPoints P.i := m.2
    refine ⟨(⟨_, hmN⟩ : normalizerPoints P.i) • x, ?_⟩
    exact (P.toValuationBuildingData.normalizer_smul_apartmentMap ⟨_, hmN⟩ x).symm
  · exact P.facetZeroStabilizer_zeroFacetTranslate _ _

/-- An element of `G(F)^0` stabilizing `A(S)` lies in `N(F)`. -/
theorem mem_normalizerPoints_of_smul_apartmentImage {g : P.zeroSubgroup}
    (hg : (g : rationalPoints G) • P.apartmentImage = P.apartmentImage) :
    (g : rationalPoints G) ∈ normalizerPoints P.i := by
  have h₁ := P.facetStabilizersIn_smul g P.apartmentImage
  have h₂ := hT.facetStabilizersIn_apartmentImage hCa
  have h₃ : restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen g =
      restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen 1 := by
    calc restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen g
        = restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen (g * 1) := by
          rw [mul_one]
      _ = conjugateSubgroup g ''
            restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen 1 :=
          (hT.isTitsSystem.image_conjugateSubgroup_restrictedApartment g 1).symm
      _ = conjugateSubgroup g '' P.facetStabilizersIn P.apartmentImage := by rw [h₂]
      _ = P.facetStabilizersIn ((g : rationalPoints G) • P.apartmentImage) := h₁.symm
      _ = P.facetStabilizersIn P.apartmentImage := by rw [hg]
      _ = _ := h₂
  exact Subgroup.mem_subgroupOf.mp
    (hT.isTitsSystem.mem_normalizer_of_restrictedApartment_eq hT.isSaturated h₃)

/-- KP Proposition 7.6.8, first claim: the stabilizer of `A(S)` in `G(F)` is
`N(F)`, given the decomposition `G(F) = G(F)^0 N(F)` (which follows from
KP Fact 2.6.22). -/
theorem hasNormalizerApartmentStabilizer
    (hprod : ∀ g : rationalPoints G, ∃ k ∈ P.zeroSubgroup,
      ∃ n ∈ normalizerPoints P.toValuationBuildingData.i, g = k * n) :
    P.HasNormalizerApartmentStabilizer := by
  refine P.toValuationBuildingData.hasNormalizerApartmentStabilizer_iff.mpr ?_
  intro g hg
  obtain ⟨k, hk, n, hn, hgkn⟩ := hprod g
  have hnA : n • P.apartmentImage = P.apartmentImage :=
    MulAction.mem_stabilizer_iff.mp
      (P.toValuationBuildingData.normalizerPoints_le_stabilizer_apartmentImage hn)
  have hkA : ((⟨k, hk⟩ : P.zeroSubgroup) : rationalPoints G) • P.apartmentImage =
      P.apartmentImage := by
    change k • P.apartmentImage = P.apartmentImage
    calc k • P.apartmentImage = k • (n • P.apartmentImage) := by rw [hnA]
      _ = (k * n) • P.apartmentImage := (mul_smul k n _).symm
      _ = g • P.apartmentImage := by rw [hgkn]
      _ = P.apartmentImage := hg
  have hkN : k ∈ normalizerPoints P.toValuationBuildingData.i := by
    have h₁ := hT.mem_normalizerPoints_of_smul_apartmentImage hCa (g := ⟨k, hk⟩) hkA
    exact h₁
  rw [hgkn]
  exact Subgroup.mul_mem _ hkN hn


/-- KP Proposition 7.6.8, first claim, from KP Fact 2.6.22. -/
theorem hasNormalizerApartmentStabilizer_of_simplyConnectedCentralizerProduct
    (hfact : SimplyConnectedCentralizerProductStatement.{u}) :
    P.HasNormalizerApartmentStabilizer :=
  hT.hasNormalizerApartmentStabilizer hCa (exists_zero_mul_normalizer hfact)

end IsBuildingTitsSystem

end Langlands.Geometry.Building.ParahoricBuildingData
