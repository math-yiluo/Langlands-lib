import Langlands.Group.TitsBorelThickness
import Langlands.Geometry.Building.TitsRealizationChambers

/-! # Chamber counts from the supplied Tits comparison -/

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

/-- Chambers containing a facet correspond to the Borel conjugates below its stabilizer. -/
def realizationChambersContainingEquivBorelsBelow (Fa : R.complex.facets) :
    ↥(AbstractBuilding.chambersContaining R.complex.facets Fa.val) ≃
      ↥(borelsBelow (P.chamberZeroStabilizerIn Ca)
        (P.facetZeroStabilizer (R.realize Fa))) :=
  Equiv.ofBijective
    (fun C =>
      let Fc : R.complex.facets := ⟨C.val, C.property.1.1⟩
      ⟨P.facetZeroStabilizer (R.realize Fc),
        (hT.realization_isChamber_iff_stabilizer R hR Fc).mp C.property.1,
        (hT.facetPrecedes_iff _ _).mp ((hR Fa Fc).mp C.property.2)⟩)
    (by
      constructor
      · intro C D hCD
        have hreal : R.realize ⟨C.val, C.property.1.1⟩ =
            R.realize ⟨D.val, D.property.1.1⟩ :=
          hT.bijOn_facetZeroStabilizer.injOn (Set.mem_univ _) (Set.mem_univ _)
            (congrArg Subtype.val hCD)
        apply Subtype.ext
        exact congrArg (fun Fc : R.complex.facets => Fc.val) (R.realize.injective hreal)
      · rintro ⟨H, ⟨⟨g, hg⟩, hH⟩⟩
        obtain ⟨Fd, hFd⟩ := hT.exists_facetZeroStabilizer_eq
          (hT.isTitsSystem.isAdmissibleParabolic_conjugate_borel g)
        let Cd := R.realize.symm Fd
        have hCd : P.facetZeroStabilizer (R.realize Cd) = H := by
          simpa only [Cd, Equiv.apply_symm_apply] using hFd.trans hg.symm
        have hch : AbstractBuilding.IsChamber R.complex.facets Cd.val :=
          hT.realization_isChamber_of_stabilizer_eq_conjugate_borel R hR Cd g
            (hCd.trans hg)
        have hsub : Fa.val ⊆ Cd.val := by
          apply (hR Fa Cd).mpr
          apply (hT.facetPrecedes_iff _ _).mpr
          rw [hCd]
          exact hH
        exact ⟨⟨Cd.val, hch, hsub⟩, Subtype.ext hCd⟩)

/-- The correspondence counts actual chambers, including when either set is infinite. -/
theorem realization_encard_chambersContaining (Fa : R.complex.facets) :
    (AbstractBuilding.chambersContaining R.complex.facets Fa.val).encard =
      (borelsBelow (P.chamberZeroStabilizerIn Ca)
        (P.facetZeroStabilizer (R.realize Fa))).encard :=
  Set.encard_congr (hT.realizationChambersContainingEquivBorelsBelow R hR Fa)

/-- Every proper face of a chamber is contained in at least three chambers. -/
theorem realization_three_le_encard_chambersContaining_of_ssubset
    {Fa Fc : R.complex.facets}
    (hFc : AbstractBuilding.IsChamber R.complex.facets Fc.val)
    (hface : Fa.val ⊂ Fc.val) :
    3 ≤ (AbstractBuilding.chambersContaining R.complex.facets Fa.val).encard := by
  obtain ⟨g, hFcstab⟩ := (hT.realization_isChamber_iff_stabilizer R hR Fc).mp hFc
  have hlt : conjugateSubgroup g (P.chamberZeroStabilizerIn Ca) <
      P.facetZeroStabilizer (R.realize Fa) := by
    constructor
    · rw [← hFcstab]
      exact (hT.facetPrecedes_iff _ _).mp ((hR Fa Fc).mp hface.subset)
    · intro hle
      have hCA : Fc.val ⊆ Fa.val := by
        apply (hR Fc Fa).mpr
        apply (hT.facetPrecedes_iff _ _).mpr
        rwa [hFcstab]
      exact hface.not_superset hCA
  rw [hT.realization_encard_chambersContaining R hR Fa]
  exact hT.isTitsSystem.three_le_encard_borelsBelow_of_conjugate_lt g hlt

/-- The chamber-count clause in BL1, without a gallery-connectedness assumption. -/
theorem realization_three_le_encard_chambersContaining :
    ∀ A, AbstractBuilding.IsCodimOneFacet R.complex.facets A →
      3 ≤ (AbstractBuilding.chambersContaining R.complex.facets A).encard := by
  rintro A ⟨C, hC, hAC⟩
  exact hT.realization_three_le_encard_chambersContaining_of_ssubset R hR
    (Fa := ⟨A, hAC.1⟩) (Fc := ⟨C, hC.1⟩) hC hAC.ssubset

end IsBuildingTitsSystem
end Langlands.Geometry.Building.ParahoricBuildingData
