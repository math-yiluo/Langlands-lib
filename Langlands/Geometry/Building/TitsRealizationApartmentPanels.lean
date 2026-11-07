import Langlands.Group.TitsApartmentPanels
import Langlands.Geometry.Building.TitsRealizationApartmentFaces

/-! # Exact chamber counts over panels in actual apartments -/

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
  (R : P.toValuationBuildingData.PolysimplicialRealization) (hR : R.IsFaceCompatible)
include hT hR

/-- Codimension one in an apartment is also codimension one in the full complex. -/
theorem realization_isCodimOneFace_of_apartment
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    {A C : Set (∀ i, R.V i)}
    (hAC : AbstractBuilding.IsCodimOneFace (R.apartmentComplex Y) A C) :
    AbstractBuilding.IsCodimOneFace R.complex.facets A C := by
  have hsub := hT.realization_isSubcomplex_apartmentComplex R hR hY
  refine ⟨hsub.1 hAC.1, hsub.1 hAC.2.1, hAC.ssubset, ?_⟩
  intro D hD hAD hDC
  exact hAC.2.2.2 D (hsub.2 C hAC.2.1 D hD hDC.subset) hAD hDC

/-- Reverse stabilizer inclusion turns a codimension-one face into an admissible cover. -/
theorem realization_stabilizer_eq_of_isCodimOneFace
    {Fa Fc : R.complex.facets}
    (hAC : AbstractBuilding.IsCodimOneFace R.complex.facets Fa.val Fc.val)
    {Q : Subgroup P.zeroSubgroup}
    (hQ : IsAdmissibleParabolic (P.chamberZeroStabilizerIn Ca) π Sgen Q)
    (hCQ : P.facetZeroStabilizer (R.realize Fc) < Q)
    (hQA : Q ≤ P.facetZeroStabilizer (R.realize Fa)) :
    Q = P.facetZeroStabilizer (R.realize Fa) := by
  obtain ⟨Fd, hFd⟩ := hT.exists_facetZeroStabilizer_eq hQ
  let Cd := R.realize.symm Fd
  have hCd : P.facetZeroStabilizer (R.realize Cd) = Q := by
    simpa only [Cd, Equiv.apply_symm_apply] using hFd
  have hAD : Fa.val ⊆ Cd.val := by
    apply (hR Fa Cd).mpr
    apply (hT.facetPrecedes_iff _ _).mpr
    rwa [hCd]
  have hDC : Cd.val ⊂ Fc.val := by
    constructor
    · apply (hR Cd Fc).mpr
      apply (hT.facetPrecedes_iff _ _).mpr
      rw [hCd]
      exact hCQ.le
    · intro hCD
      apply hCQ.not_ge
      rw [← hCd]
      exact (hT.facetPrecedes_iff _ _).mp ((hR Fc Cd).mp hCD)
  have heq : Fa = Cd := by
    apply Subtype.ext
    apply Set.Subset.antisymm hAD
    by_contra hDA
    exact hAC.2.2.2 Cd.val Cd.property ⟨hAD, hDA⟩ hDC
  rw [← hCd, ← heq]

/-- Containing apartment chambers correspond to the apartment Borels below the stabilizer. -/
def realizationApartmentChambersContainingEquivBorelsBelow
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y) (a : P.zeroSubgroup)
    (ha : restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a =
      P.facetStabilizersIn Y) (Fa : R.complex.facets) :
    ↥(AbstractBuilding.chambersContaining (R.apartmentComplex Y) Fa.val) ≃
      ↥(apartmentBorelsBelow (P.chamberZeroStabilizerIn Ca) P.normalizerInZero a
        (P.facetZeroStabilizer (R.realize Fa))) :=
  Equiv.ofBijective
    (fun C =>
      let Fc : R.complex.facets := ⟨C.val, C.property.1.1.choose⟩
      let hC := (hT.realization_isChamber_apartmentComplex_iff R hR hY C.val).mp C.property.1
      ⟨P.facetZeroStabilizer (R.realize Fc), by
        rw [hT.isTitsSystem.apartmentBorelsBelow_eq_inter]
        refine ⟨⟨(hT.realization_isChamber_iff_stabilizer R hR Fc).mp hC.1,
          (hT.facetPrecedes_iff _ _).mp ((hR Fa Fc).mp C.property.2)⟩, ?_⟩
        rw [ha]
        exact ⟨R.realize Fc, hC.2.choose_spec, rfl⟩⟩)
    (by
      constructor
      · intro C D hCD
        have hreal : R.realize ⟨C.val, C.property.1.1.choose⟩ =
            R.realize ⟨D.val, D.property.1.1.choose⟩ :=
          hT.bijOn_facetZeroStabilizer.injOn (Set.mem_univ _) (Set.mem_univ _)
            (congrArg Subtype.val hCD)
        apply Subtype.ext
        exact congrArg (fun Fc : R.complex.facets => Fc.val) (R.realize.injective hreal)
      · rintro ⟨H, hH⟩
        rw [hT.isTitsSystem.apartmentBorelsBelow_eq_inter] at hH
        obtain ⟨⟨⟨g, hg⟩, hle⟩, hapt⟩ := hH
        rw [ha] at hapt
        obtain ⟨Fd, hFdY, hFd⟩ := hapt
        let Cd := R.realize.symm Fd
        have hCd : P.facetZeroStabilizer (R.realize Cd) = H := by
          simpa only [Cd, Equiv.apply_symm_apply] using hFd
        have hCdY : Cd.val ∈ R.apartmentComplex Y := by
          refine ⟨Cd.property, ?_⟩
          change (R.realize Cd).val ⊆ Y
          change Fd.val ⊆ Y at hFdY
          simpa only [Cd, Equiv.apply_symm_apply] using hFdY
        have hch : AbstractBuilding.IsChamber (R.apartmentComplex Y) Cd.val :=
          (hT.realization_isChamber_apartmentComplex_iff R hR hY Cd.val).mpr
            ⟨hT.realization_isChamber_of_stabilizer_eq_conjugate_borel R hR Cd g
              (hCd.trans hg), hCdY⟩
        have hsub : Fa.val ⊆ Cd.val := by
          apply (hR Fa Cd).mpr
          apply (hT.facetPrecedes_iff _ _).mpr
          rwa [hCd]
        exact ⟨⟨Cd.val, hch, hsub⟩, Subtype.ext hCd⟩)

theorem realization_encard_apartment_chambersContaining
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y) (a : P.zeroSubgroup)
    (ha : restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a =
      P.facetStabilizersIn Y) (Fa : R.complex.facets) :
    (AbstractBuilding.chambersContaining (R.apartmentComplex Y) Fa.val).encard =
      (apartmentBorelsBelow (P.chamberZeroStabilizerIn Ca) P.normalizerInZero a
        (P.facetZeroStabilizer (R.realize Fa))).encard :=
  Set.encard_congr (hT.realizationApartmentChambersContainingEquivBorelsBelow
    R hR hY a ha Fa)

/-- A panel of an apartment chamber lies in exactly two chambers of that apartment. -/
theorem realization_encard_apartment_chambersContaining_eq_two_of_isCodimOneFace
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y)
    {Fa Fc : R.complex.facets}
    (hFc : AbstractBuilding.IsChamber (R.apartmentComplex Y) Fc.val)
    (hAC : AbstractBuilding.IsCodimOneFace (R.apartmentComplex Y) Fa.val Fc.val) :
    (AbstractBuilding.chambersContaining (R.apartmentComplex Y) Fa.val).encard = 2 := by
  obtain ⟨a, ha⟩ := hT.exists_restrictedApartment_eq hY
  have hFc' := (hT.realization_isChamber_apartmentComplex_iff R hR hY Fc.val).mp hFc
  have hCap : P.facetZeroStabilizer (R.realize Fc) ∈
      restrictedApartment (P.chamberZeroStabilizerIn Ca) π Sgen a := by
    rw [ha]
    exact ⟨R.realize Fc, hFc'.2.choose_spec, rfl⟩
  have hCb : P.facetZeroStabilizer (R.realize Fc) ∈
      apartmentBorelsBelow (P.chamberZeroStabilizerIn Ca) P.normalizerInZero a
        (P.facetZeroStabilizer (R.realize Fc)) := by
    rw [hT.isTitsSystem.apartmentBorelsBelow_eq_inter]
    exact ⟨⟨(hT.realization_isChamber_iff_stabilizer R hR Fc).mp hFc'.1, le_rfl⟩, hCap⟩
  obtain ⟨⟨n, hn⟩, _⟩ := hCb
  have hCQ : conjugateSubgroup (a * n) (P.chamberZeroStabilizerIn Ca) <
      P.facetZeroStabilizer (R.realize Fa) := by
    rw [← hn]
    constructor
    · exact (hT.facetPrecedes_iff _ _).mp ((hR Fa Fc).mp hAC.ssubset.subset)
    · intro hle
      exact hAC.ssubset.not_superset
        ((hR Fc Fa).mpr ((hT.facetPrecedes_iff _ _).mpr hle))
  have hcount := hT.isTitsSystem.encard_apartmentBorelsBelow_eq_two_of_conjugate_cover
    (a * n) (hT.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ (R.realize Fa))) hCQ
    (by
      intro Q hQ hBQ hQA
      apply hT.realization_stabilizer_eq_of_isCodimOneFace R hR
        (hT.realization_isCodimOneFace_of_apartment R hR hY hAC) hQ
      · rwa [hn]
      · exact hQA)
  rw [apartmentBorelsBelow_mul_normalizer] at hcount
  rw [hT.realization_encard_apartment_chambersContaining R hR hY a ha Fa]
  exact hcount

/-- The panel-count clause of BL2, without the chamber-complex hypotheses. -/
theorem realization_encard_apartment_chambersContaining_eq_two
    {Y : Set P.ReducedBuilding} (hY : P.IsApartment Y) :
    ∀ A, AbstractBuilding.IsCodimOneFacet (R.apartmentComplex Y) A →
      (AbstractBuilding.chambersContaining (R.apartmentComplex Y) A).encard = 2 := by
  rintro A ⟨C, hC, hAC⟩
  exact hT.realization_encard_apartment_chambersContaining_eq_two_of_isCodimOneFace
    R hR hY (Fa := ⟨A, hAC.1.choose⟩) (Fc := ⟨C, hC.1.choose⟩) hC hAC

end IsBuildingTitsSystem
end Langlands.Geometry.Building.ParahoricBuildingData
