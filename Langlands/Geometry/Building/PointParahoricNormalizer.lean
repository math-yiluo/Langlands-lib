import Langlands.Geometry.Building.PointSharpExchange
import Langlands.Geometry.Building.ChamberSharpCore
import Langlands.Geometry.Building.KPParahoricProduct
import Langlands.Geometry.Building.NormalizerApartmentActionKernel
import Langlands.Geometry.Building.ApartmentRootCover
import Langlands.Geometry.Building.AffineChamberTransitivity
import Langlands.GroupScheme.Rational.GenericCocharacter

/-! # Actual normalizer intersections at points and chambers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace AffineRootSystem

/-- Local constancy of root signs makes a chamber span its whole affine space. -/
theorem IsChamber.affineSpan_eq_top
    {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    {Ψ : Set (A →ᵃ[ℝ] ℝ)}
    (hΨ : IsLocallyFiniteReflectionArrangement Ψ)
    {C : Set A} (hC : IsChamber Ψ C) : affineSpan ℝ C = ⊤ := by
  obtain ⟨x, hx, rfl⟩ := hC
  have hxspan := subset_affineSpan ℝ (facet Ψ x) (mem_facet_self Ψ x)
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x, hxspan⟩).mp
  apply top_unique
  intro v _
  obtain ⟨ε, hε, hsign⟩ := GalleryGeometry.exists_pos_of_eventually
    (GalleryGeometry.eventually_sign_smul_vadd hΨ x v)
  have hpoint : ε • v +ᵥ x ∈ facet Ψ x :=
    fun ψ hψ => (hsign ψ hψ (hx ψ hψ)).symm
  have hd : ε • v ∈ (affineSpan ℝ (facet Ψ x)).direction := by
    simpa only [vadd_vsub] using (affineSpan ℝ (facet Ψ x)).vsub_mem_direction
      (subset_affineSpan ℝ (facet Ψ x) hpoint) hxspan
  simpa only [smul_smul, inv_mul_cancel₀ hε.ne', one_smul] using
    (affineSpan ℝ (facet Ψ x)).direction.smul_mem ε⁻¹ hd

end AffineRootSystem

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- Point exchange and opposite-cell separation force every normalizing sharp
fixer element to fix the actual apartment point. -/
theorem normalizer_smul_eq_self_of_mem_sharpFixer
    (hB : B.apartment.SatisfiesApartmentAxioms B.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization B.i)
    (x : B.Apartment) (n : normalizerPoints B.i)
    (hn : (n : rationalPoints G) ∈ B.sharpFixer {x}) : n • x = x := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  obtain ⟨ν, hν⟩ :=
    B.isMaximalSplitTorus.isSplitSubtorus.1.exists_genericCocharacter B.i
  obtain ⟨vw, ⟨v, hv, w, hw, rfl⟩, m, hm, heq⟩ :=
    B.sharpFixer_subset_mul_sharpNormalizerStabilizer hB hrank x ν hν hn
  change v * w * m = (n : rationalPoints G) at heq
  obtain ⟨_, hmN, hmx⟩ := KPApartmentData.mem_sharpNormalizerStabilizer.mp hm
  let m' : normalizerPoints B.i := ⟨m, hmN⟩
  let q : normalizerPoints B.i := n * m'⁻¹
  have hq : (q : rationalPoints G) = v * w := by
    change (n : rationalPoints G) * m⁻¹ = v * w
    rw [← heq, mul_inv_cancel_right]
  have hvU :=
    (B.apartment.positiveChamberRootGroups_le_sharpUnipotentPoints x (-ν) hv).1
  have hwU :=
    (B.apartment.positiveChamberRootGroups_le_sharpUnipotentPoints x ν hw).1
  have hvopp : v ∈ (Dynamic.unipotent
      (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ B.i))).carrier
        (Over.mk (𝟙 _)) := by
    rw [← groupHom_neg_comp_eq_oppositeCocharacter B.i ν]
    exact hvU
  have hq1 : q = 1 :=
    normalizer_eq_one_of_unipotent_product B.i ν q ⟨v, hvopp⟩ ⟨w, hwU⟩ hq
  have hnm : n = m' := mul_inv_eq_one.mp hq1
  rw [hnm]
  exact hmx

/-- The normalizer part of the singleton sharp fixer equals its point stabilizer. -/
theorem sharpNormalizer_eq_sharpNormalizerStabilizer
    (hB : B.apartment.SatisfiesApartmentAxioms B.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization B.i) (x : B.Apartment) :
    B.apartment.sharpNormalizer {x} = B.apartment.sharpNormalizerStabilizer x := by
  apply le_antisymm
  · intro n hn
    exact KPApartmentData.mem_sharpNormalizerStabilizer.mpr
      ⟨hn.2, hn.1, B.normalizer_smul_eq_self_of_mem_sharpFixer hB hrank x ⟨n, hn.1⟩ hn.2⟩
  · exact B.apartment.sharpNormalizerStabilizer_le_sharpNormalizer x

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- A normalizer point in the actual full point parahoric fixes that point. -/
theorem normalizer_smul_eq_self_of_mem_parahoricAt
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (x : P.Apartment) (n : normalizerPoints P.i)
    (hn : (n : rationalPoints G) ∈ P.parahoricAt x) : n • x = x := by
  obtain ⟨z, hz, g, hg, heq⟩ := P.mem_parahoric_iff.mp hn
  have hzN : rationalPoints.map P.centralizer.j z ∈ normalizerPoints P.i :=
    (P.centralizer.toNormalizer z).property
  have hgN : g ∈ normalizerPoints P.i := by
    have hmem := (normalizerPoints P.i).mul_mem
      ((normalizerPoints P.i).inv_mem hzN) n.property
    rw [← heq, inv_mul_cancel_left] at hmem
    exact hmem
  have hng : P.centralizer.toNormalizer z * (⟨g, hgN⟩ : normalizerPoints P.i) = n :=
    Subtype.ext heq
  rw [← hng, mul_smul,
    P.toValuationBuildingData.normalizer_smul_eq_self_of_mem_sharpFixer
      hP hrank x ⟨g, hgN⟩ hg]
  exact P.isOmegaCompatible.smul_eq_self
    (P.zeroDatum.centralizerZero_le_rationalCommonNormKernel hz) x

/-- A normalizer element of a chamber parahoric acts trivially on the apartment. -/
theorem normalizerAffineEquiv_eq_one_of_mem_chamber_parahoric
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (n : normalizerPoints P.i) (hn : (n : rationalPoints G) ∈ P.parahoric C) :
    P.apartment.normalizerAffineEquiv n = 1 := by
  apply AffineEquiv.ext_on
    (hC.affineSpan_eq_top hP.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement)
  intro x hx
  exact P.normalizer_smul_eq_self_of_mem_parahoricAt hP hrank x n
    (P.parahoric_anti (Set.singleton_subset_iff.mpr hx) hn)

/-- With the actual cover comparison, the chamber normalizer intersection is
exactly the actual centralizer-zero image. -/
theorem zeroNormalizer_eq_map_centralizerZero_of_isChamber
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    P.zeroNormalizer C = P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  apply le_antisymm
  · intro n hn
    apply (P.mem_normalizerZero_iff (n := (⟨n, hn.1⟩ : normalizerPoints P.i))).mp
    apply (P.normalizerAffineEquiv_eq_one_iff_of_mem_normalizerZeroComponent
      hZ ⟨n, hn.1⟩ (P.parahoric_le_zeroSubgroup hP C hn.2)).mp
    exact P.normalizerAffineEquiv_eq_one_of_mem_chamber_parahoric
      hP hrank hC ⟨n, hn.1⟩ hn.2
  · exact le_inf
      (fun _ hn => centralizerPoints_le_normalizerPoints P.i
        (P.map_centralizerZero_le_centralizerPoints hn))
      (P.map_centralizerZero_le_parahoric C)

/-- The identity on ambient rational points identifies the chamber normalizer
intersection with the actual centralizer-zero image. -/
def chamberZeroNormalizerEquivCentralizerZeroImage
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    P.zeroNormalizer C ≃* P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  MulEquiv.subgroupCongr (P.zeroNormalizer_eq_map_centralizerZero_of_isChamber hP hrank hZ hC)

/-- The chamber equivalence preserves the ambient rational point. -/
@[simp] theorem chamberZeroNormalizerEquivCentralizerZeroImage_apply_coe
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (n : P.zeroNormalizer C) :
    ((P.chamberZeroNormalizerEquivCentralizerZeroImage hP hrank hZ hC n :
      P.centralizerZero.map (rationalPoints.map P.centralizer.j)) : rationalPoints G) = n :=
  rfl

end ParahoricBuildingData
end Langlands.Geometry.Building
