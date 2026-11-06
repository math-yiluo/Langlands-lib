import Langlands.Group.TitsBorelChambers
import Langlands.Geometry.Building.FullValidity.ChamberAxioms
import Langlands.Geometry.Building.FullValidity.Realization

/-! # Chambers of a supplied realization from the Tits comparison -/

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

/-- A facet with a conjugate Iwahori stabilizer is a chamber. -/
theorem realization_isChamber_of_stabilizer_eq_conjugate_borel
    (Fc : R.complex.facets) (g : P.zeroSubgroup)
    (hFc : P.facetZeroStabilizer (R.realize Fc) =
      conjugateSubgroup g (P.chamberZeroStabilizerIn Ca)) :
    AbstractBuilding.IsChamber R.complex.facets Fc.val := by
  refine ⟨Fc.property, ?_⟩
  intro D hD hCD
  let Fd : R.complex.facets := ⟨D, hD⟩
  have hle : P.facetZeroStabilizer (R.realize Fd) ≤
      conjugateSubgroup g (P.chamberZeroStabilizerIn Ca) := by
    rw [← hFc]
    exact (hT.facetPrecedes_iff _ _).mp ((hR Fc Fd).mp hCD)
  have heq := hT.isTitsSystem.eq_conjugate_borel_of_isAdmissible_of_le
    (hT.bijOn_facetZeroStabilizer.mapsTo (Set.mem_univ (R.realize Fd))) g hle
  have hreal : R.realize Fd = R.realize Fc :=
    hT.bijOn_facetZeroStabilizer.injOn (Set.mem_univ _) (Set.mem_univ _)
      (heq.trans hFc.symm)
  exact (congrArg Subtype.val (R.realize.injective hreal)).subset

/-- Every facet lies in a chamber with a conjugate Iwahori stabilizer. -/
theorem realization_exists_chamber_with_stabilizer (Fc : R.complex.facets) :
    ∃ (Cd : R.complex.facets) (g : P.zeroSubgroup),
      AbstractBuilding.IsChamber R.complex.facets Cd.val ∧ Fc.val ⊆ Cd.val ∧
        P.facetZeroStabilizer (R.realize Cd) =
          conjugateSubgroup g (P.chamberZeroStabilizerIn Ca) := by
  obtain ⟨g, hg⟩ := hT.isParabolic_facetZeroStabilizer (R.realize Fc)
  obtain ⟨Fd, hFd⟩ := hT.exists_facetZeroStabilizer_eq
    (hT.isTitsSystem.isAdmissibleParabolic_conjugate_borel g)
  let Cd := R.realize.symm Fd
  have hCd : P.facetZeroStabilizer (R.realize Cd) =
      conjugateSubgroup g (P.chamberZeroStabilizerIn Ca) := by
    simpa only [Cd, Equiv.apply_symm_apply] using hFd
  refine ⟨Cd, g,
    hT.realization_isChamber_of_stabilizer_eq_conjugate_borel R hR Cd g hCd, ?_, hCd⟩
  apply (hR Fc Cd).mpr
  apply (hT.facetPrecedes_iff _ _).mpr
  rw [hCd]
  exact hg

/-- Chambers are exactly the facets with a conjugate Iwahori stabilizer. -/
theorem realization_isChamber_iff_stabilizer (Fc : R.complex.facets) :
    AbstractBuilding.IsChamber R.complex.facets Fc.val ↔
      ∃ g : P.zeroSubgroup, P.facetZeroStabilizer (R.realize Fc) =
        conjugateSubgroup g (P.chamberZeroStabilizerIn Ca) := by
  constructor
  · intro hFc
    obtain ⟨Cd, g, _, hsub, heq⟩ :=
      hT.realization_exists_chamber_with_stabilizer R hR Fc
    have hsame : Fc = Cd := Subtype.ext (Set.Subset.antisymm hsub (hFc.2 Cd.property hsub))
    exact ⟨g, hsame ▸ heq⟩
  · rintro ⟨g, hg⟩
    exact hT.realization_isChamber_of_stabilizer_eq_conjugate_borel R hR Fc g hg

/-- The facet-extension clause of a chamber complex, with no gallery premise. -/
theorem realization_exists_chamber :
    ∀ A ∈ R.complex.facets, ∃ C,
      AbstractBuilding.IsChamber R.complex.facets C ∧ A ⊆ C := by
  intro A hA
  obtain ⟨Cd, _, hCd, hsub, _⟩ :=
    hT.realization_exists_chamber_with_stabilizer R hR ⟨A, hA⟩
  exact ⟨Cd.val, hCd, hsub⟩

/-- A chosen chamber containing the supplied facet. -/
def realizationContainingChamber (Fc : R.complex.facets) : R.complex.facets :=
  (hT.realization_exists_chamber_with_stabilizer R hR Fc).choose

theorem realizationContainingChamber_spec (Fc : R.complex.facets) :
    AbstractBuilding.IsChamber R.complex.facets
        (hT.realizationContainingChamber R hR Fc).val ∧
      Fc.val ⊆ (hT.realizationContainingChamber R hR Fc).val := by
  obtain ⟨g, hCd, hsub, _⟩ :=
    (hT.realization_exists_chamber_with_stabilizer R hR Fc).choose_spec
  exact ⟨hCd, hsub⟩

end IsBuildingTitsSystem
end Langlands.Geometry.Building.ParahoricBuildingData
