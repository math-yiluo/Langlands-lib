import Langlands.Geometry.Building.PointParahoricNormalizer
import Langlands.Geometry.Building.CentralizerParahoricReduction

/-! # Centralizer intersections from actual point fixation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- A centralizer point of a nonempty generated parahoric has norm one:
point exchange fixes a point, and the ambient zero subgroup has norm one. -/
theorem mem_centralizerNormKernel_of_mem_parahoric
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    {Ω : Set P.Apartment} (hΩ : Ω.Nonempty)
    {z : rationalPoints P.centralizer.Z}
    (hz : rationalPoints.map P.centralizer.j z ∈ P.parahoric Ω) :
    z ∈ rationalCommonNormKernel P.centralizer.Z := by
  obtain ⟨x, hx⟩ := hΩ
  have hzP : rationalPoints.map P.centralizer.j z ∈ P.parahoricAt x :=
    P.parahoric_anti (Set.singleton_subset_iff.mpr hx) hz
  exact P.toValuationBuildingData.mem_rationalCommonNormKernel_of_smul_eq z
    (P.zeroDatum.zeroSubgroup_le_rationalCommonNormKernel
      (P.parahoric_le_zeroSubgroup hP Ω hz))
    (P.normalizer_smul_eq_self_of_mem_parahoricAt
      hP hrank x (P.centralizer.toNormalizer z) hzP)

/-- The explicit cover comparison turns the preceding norm-one consequence
into membership in the actual centralizer-zero subgroup. -/
theorem mem_centralizerZero_of_mem_parahoric_of_rankOneFactorization
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {Ω : Set P.Apartment} (hΩ : Ω.Nonempty)
    {z : rationalPoints P.centralizer.Z}
    (hz : rationalPoints.map P.centralizer.j z ∈ P.parahoric Ω) :
    z ∈ P.centralizerZero := by
  have hi := P.zeroDatum.centralizerZeroIntersection_of_coverImage hZ
  change P.zeroSubgroup.comap (rationalPoints.map P.centralizer.j) ⊓
    rationalCommonNormKernel P.centralizer.Z = P.centralizerZero at hi
  rw [← hi]
  exact ⟨P.parahoric_le_zeroSubgroup hP Ω hz,
    P.mem_centralizerNormKernel_of_mem_parahoric hP hrank hΩ hz⟩

/-- Rank-one point exchange and the actual cover comparison suffice for the
centralizer intersection of every nonempty full generated parahoric. -/
theorem centralizer_inf_parahoric_eq_of_rankOneFactorization
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {Ω : Set P.Apartment} (hΩ : Ω.Nonempty) :
    centralizerPoints P.i ⊓ P.parahoric Ω =
      P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  apply le_antisymm _ (P.map_centralizerZero_le_centralizer_inf_parahoric Ω)
  rintro g ⟨hgZ, hgP⟩
  rw [← torusCentralizer_carrier_base, ← P.centralizer.isRepresentedBy.2] at hgZ
  obtain ⟨z, rfl⟩ := hgZ
  exact ⟨z,
    P.mem_centralizerZero_of_mem_parahoric_of_rankOneFactorization hP hrank hZ hΩ hgP,
    rfl⟩

/-- The same local proof supplies the existing centralizer-parahoric
proposition once the two explicit algebraic inputs are provided. -/
theorem centralizerParahoricIntersection_of_rankOneFactorization
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement) :
    P.CentralizerParahoricIntersectionStatement :=
  fun hP _ hΩ => P.centralizer_inf_parahoric_eq_of_rankOneFactorization hP hrank hZ hΩ

/-- The identity on ambient rational points identifies the actual centralizer
intersection with the actual centralizer-zero image. -/
def centralizerParahoricEquivCentralizerZeroImage
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {Ω : Set P.Apartment} (hΩ : Ω.Nonempty) :
    ↥(centralizerPoints P.i ⊓ P.parahoric Ω) ≃*
      P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  MulEquiv.subgroupCongr
    (P.centralizer_inf_parahoric_eq_of_rankOneFactorization hP hrank hZ hΩ)

/-- The equivalence preserves the ambient rational point. -/
@[simp] theorem centralizerParahoricEquivCentralizerZeroImage_apply_coe
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {Ω : Set P.Apartment} (hΩ : Ω.Nonempty)
    (g : ↥(centralizerPoints P.i ⊓ P.parahoric Ω)) :
    ((P.centralizerParahoricEquivCentralizerZeroImage hP hrank hZ hΩ g :
      P.centralizerZero.map (rationalPoints.map P.centralizer.j)) : rationalPoints G) = g :=
  rfl

end Langlands.Geometry.Building.ParahoricBuildingData
